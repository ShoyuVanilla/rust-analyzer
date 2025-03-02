use std::mem;

use hir_def::GenericDefId;
use rustc_hash::FxHashMap;
use rustc_type_ir::error::TypeError;
use rustc_type_ir::inherent::{Const as _, IntoKind, Ty as _};
use rustc_type_ir::relate::VarianceDiagInfo;
use rustc_type_ir::visit::{TypeVisitable, TypeVisitableExt};
use rustc_type_ir::{AliasRelationDirection, AliasTyKind, ConstVid, InferConst, InferCtxtLike, InferTy, RegionKind, RustIr, TermKind, TyVid, UniverseIndex, Variance};
use tracing::{debug, instrument, warn};

use super::{
    PredicateEmittingRelation, Relate, RelateResult, StructurallyRelateAliases, TypeRelation,
};
use crate::next_solver::infer::type_variable::TypeVariableValue;
use crate::next_solver::infer::unify_key::ConstVariableValue;
use crate::next_solver::infer::{InferCtxt, RegionVariableOrigin, relate};
use crate::next_solver::util::MaxUniverse;
use crate::next_solver::{AliasTy, Binder, ClauseKind, Const, ConstKind, DbInterner, DbIr, GenericArgs, PredicateKind, ProjectionPredicate, Region, Span, Term, TermVid, Ty, TyKind, TypingMode, UnevaluatedConst};

impl<'db> InferCtxt<'db> {
    /// The idea is that we should ensure that the type variable `target_vid`
    /// is equal to, a subtype of, or a supertype of `source_ty`.
    ///
    /// For this, we will instantiate `target_vid` with a *generalized* version
    /// of `source_ty`. Generalization introduces other inference variables wherever
    /// subtyping could occur. This also does the occurs checks, detecting whether
    /// instantiating `target_vid` would result in a cyclic type. We eagerly error
    /// in this case.
    ///
    /// This is *not* expected to be used anywhere except for an implementation of
    /// `TypeRelation`. Do not use this, and instead please use `At::eq`, for all
    /// other usecases (i.e. setting the value of a type var).
    #[instrument(level = "debug", skip(self, relation))]
    pub fn instantiate_ty_var<R: PredicateEmittingRelation<InferCtxt<'db>>>(
        &self,
        relation: &mut R,
        target_is_expected: bool,
        target_vid: TyVid,
        instantiation_variance: Variance,
        source_ty: Ty,
    ) -> RelateResult<()> {
        debug_assert!(self.inner.borrow_mut().type_variables().probe(target_vid).is_unknown());

        // Generalize `source_ty` depending on the current variance. As an example, assume
        // `?target <: &'x ?1`, where `'x` is some free region and `?1` is an inference
        // variable.
        //
        // Then the `generalized_ty` would be `&'?2 ?3`, where `'?2` and `?3` are fresh
        // region/type inference variables.
        //
        // We then relate `generalized_ty <: source_ty`, adding constraints like `'x: '?2` and
        // `?1 <: ?3`.
        let Generalization { value_may_be_infer: generalized_ty, has_unconstrained_ty_var } = self
            .generalize(
                relation.span(),
                relation.structurally_relate_aliases(),
                target_vid,
                instantiation_variance,
                source_ty.clone(),
            )?;

        // Constrain `b_vid` to the generalized type `generalized_ty`.
        if let TyKind::Infer(InferTy::TyVar(generalized_vid)) = generalized_ty.clone().kind() {
            self.inner.borrow_mut().type_variables().equate(target_vid, generalized_vid);
        } else {
            self.inner.borrow_mut().type_variables().instantiate(target_vid, generalized_ty.clone());
        }

        // See the comment on `Generalization::has_unconstrained_ty_var`.
        if has_unconstrained_ty_var {
            relation.register_predicates([ClauseKind::WellFormed(generalized_ty.clone().into())]);
        }

        // Finally, relate `generalized_ty` to `source_ty`, as described in previous comment.
        //
        // FIXME(#16847): This code is non-ideal because all these subtype
        // relations wind up attributed to the same spans. We need
        // to associate causes/spans with each of the relations in
        // the stack to get this right.
        if generalized_ty.is_ty_var() {
            // This happens for cases like `<?0 as Trait>::Assoc == ?0`.
            // We can't instantiate `?0` here as that would result in a
            // cyclic type. We instead delay the unification in case
            // the alias can be normalized to something which does not
            // mention `?0`.
            let (lhs, rhs, direction) = match instantiation_variance {
                Variance::Invariant => {
                    (generalized_ty.into(), source_ty.into(), AliasRelationDirection::Equate)
                }
                Variance::Covariant => {
                    (generalized_ty.into(), source_ty.into(), AliasRelationDirection::Subtype)
                }
                Variance::Contravariant => {
                    (source_ty.into(), generalized_ty.into(), AliasRelationDirection::Subtype)
                }
                Variance::Bivariant => unreachable!("bivariant generalization"),
            };

            relation.register_predicates([PredicateKind::AliasRelate(lhs, rhs, direction)]);
        } else {
            // NOTE: The `instantiation_variance` is not the same variance as
            // used by the relation. When instantiating `b`, `target_is_expected`
            // is flipped and the `instantiation_variance` is also flipped. To
            // constrain the `generalized_ty` while using the original relation,
            // we therefore only have to flip the arguments.
            //
            // ```ignore (not code)
            // ?a rel B
            // instantiate_ty_var(?a, B) # expected and variance not flipped
            // B' rel B
            // ```
            // or
            // ```ignore (not code)
            // A rel ?b
            // instantiate_ty_var(?b, A) # expected and variance flipped
            // A rel A'
            // ```
            if target_is_expected {
                relation.relate(generalized_ty, source_ty)?;
            } else {
                debug!("flip relation");
                relation.relate(source_ty, generalized_ty)?;
            }
        }

        Ok(())
    }

    /// Instantiates the const variable `target_vid` with the given constant.
    ///
    /// This also tests if the given const `ct` contains an inference variable which was previously
    /// unioned with `target_vid`. If this is the case, inferring `target_vid` to `ct`
    /// would result in an infinite type as we continuously replace an inference variable
    /// in `ct` with `ct` itself.
    ///
    /// This is especially important as unevaluated consts use their parents generics.
    /// They therefore often contain unused args, making these errors far more likely.
    ///
    /// A good example of this is the following:
    ///
    /// ```compile_fail,E0308
    /// #![feature(generic_const_exprs)]
    ///
    /// fn bind<const N: usize>(value: [u8; N]) -> [u8; 3 + 4] {
    ///     todo!()
    /// }
    ///
    /// fn main() {
    ///     let mut arr = Default::default();
    ///     arr = bind(arr);
    /// }
    /// ```
    ///
    /// Here `3 + 4` ends up as `ConstKind::Unevaluated` which uses the generics
    /// of `fn bind` (meaning that its args contain `N`).
    ///
    /// `bind(arr)` now infers that the type of `arr` must be `[u8; N]`.
    /// The assignment `arr = bind(arr)` now tries to equate `N` with `3 + 4`.
    ///
    /// As `3 + 4` contains `N` in its args, this must not succeed.
    ///
    /// See `tests/ui/const-generics/occurs-check/` for more examples where this is relevant.
    #[instrument(level = "debug", skip(self, relation))]
    pub(crate) fn instantiate_const_var<R: PredicateEmittingRelation<InferCtxt<'db>>>(
        &self,
        relation: &mut R,
        target_is_expected: bool,
        target_vid: ConstVid,
        source_ct: Const,
    ) -> RelateResult<()> {
        // FIXME(generic_const_exprs): Occurs check failures for unevaluated
        // constants and generic expressions are not yet handled correctly.
        let Generalization { value_may_be_infer: generalized_ct, has_unconstrained_ty_var } = self
            .generalize(
                relation.span(),
                relation.structurally_relate_aliases(),
                target_vid,
                Variance::Invariant,
                source_ct.clone(),
            )?;

        debug_assert!(!generalized_ct.is_ct_infer());
        if has_unconstrained_ty_var {
            panic!("unconstrained ty var when generalizing `{source_ct:?}`");
        }

        self.inner
            .borrow_mut()
            .const_unification_table()
            .union_value(target_vid, ConstVariableValue::Known { value: generalized_ct.clone() });

        // Make sure that the order is correct when relating the
        // generalized const and the source.
        if target_is_expected {
            relation.relate_with_variance(
                Variance::Invariant,
                VarianceDiagInfo::default(),
                generalized_ct,
                source_ct,
            )?;
        } else {
            relation.relate_with_variance(
                Variance::Invariant,
                VarianceDiagInfo::default(),
                source_ct,
                generalized_ct,
            )?;
        }

        Ok(())
    }

    /// Attempts to generalize `source_term` for the type variable `target_vid`.
    /// This checks for cycles -- that is, whether `source_term` references `target_vid`.
    fn generalize<T: Into<Term> + Relate<DbInterner>>(
        &self,
        span: Span,
        structurally_relate_aliases: StructurallyRelateAliases,
        target_vid: impl Into<TermVid>,
        ambient_variance: Variance,
        source_term: T,
    ) -> RelateResult<Generalization<T>> {
        assert!(!source_term.clone().has_escaping_bound_vars());
        let (for_universe, root_vid) = match target_vid.into() {
            TermVid::Ty(ty_vid) => {
                (self.probe_ty_var(ty_vid).unwrap_err(), TermVid::Ty(self.root_var(ty_vid)))
            }
            TermVid::Const(ct_vid) => (
                self.probe_const_var(ct_vid).unwrap_err(),
                TermVid::Const(
                    self.inner.borrow_mut().const_unification_table().find(ct_vid).vid,
                ),
            ),
        };

        let mut generalizer = Generalizer {
            infcx: self,
            span,
            structurally_relate_aliases,
            root_vid,
            for_universe,
            root_term: source_term.clone().into(),
            ambient_variance,
            in_alias: false,
            cache: Default::default(),
            has_unconstrained_ty_var: false,
        };

        let value_may_be_infer = generalizer.relate(source_term.clone(), source_term)?;
        let has_unconstrained_ty_var = generalizer.has_unconstrained_ty_var;
        Ok(Generalization { value_may_be_infer, has_unconstrained_ty_var })
    }
}

/// The "generalizer" is used when handling inference variables.
///
/// The basic strategy for handling a constraint like `?A <: B` is to
/// apply a "generalization strategy" to the term `B` -- this replaces
/// all the lifetimes in the term `B` with fresh inference variables.
/// (You can read more about the strategy in this [blog post].)
///
/// As an example, if we had `?A <: &'x u32`, we would generalize `&'x
/// u32` to `&'0 u32` where `'0` is a fresh variable. This becomes the
/// value of `A`. Finally, we relate `&'0 u32 <: &'x u32`, which
/// establishes `'0: 'x` as a constraint.
///
/// [blog post]: https://is.gd/0hKvIr
struct Generalizer<'me, 'db> {
    infcx: &'me InferCtxt<'db>,

    span: Span,

    /// Whether aliases should be related structurally. If not, we have to
    /// be careful when generalizing aliases.
    structurally_relate_aliases: StructurallyRelateAliases,

    /// The vid of the type variable that is in the process of being
    /// instantiated. If we find this within the value we are folding,
    /// that means we would have created a cyclic value.
    root_vid: TermVid,

    /// The universe of the type variable that is in the process of being
    /// instantiated. If we find anything that this universe cannot name,
    /// we reject the relation.
    for_universe: UniverseIndex,

    /// The root term (const or type) we're generalizing. Used for cycle errors.
    root_term: Term,

    /// After we generalize this type, we are going to relate it to
    /// some other type. What will be the variance at this point?
    ambient_variance: Variance,

    /// This is set once we're generalizing the arguments of an alias.
    ///
    /// This is necessary to correctly handle
    /// `<T as Bar<<?0 as Foo>::Assoc>::Assoc == ?0`. This equality can
    /// hold by either normalizing the outer or the inner associated type.
    in_alias: bool,

    cache: FxHashMap<(Ty, Variance, bool), Ty>,

    /// See the field `has_unconstrained_ty_var` in `Generalization`.
    has_unconstrained_ty_var: bool,
}

impl Generalizer<'_, '_> {
    /// Create an error that corresponds to the term kind in `root_term`
    fn cyclic_term_error(&self) -> TypeError<DbInterner> {
        match self.root_term.clone().kind() {
            TermKind::Ty(ty) => TypeError::CyclicTy(ty),
            TermKind::Const(ct) => TypeError::CyclicConst(ct),
        }
    }

    /// Create a new type variable in the universe of the target when
    /// generalizing an alias. This has to set `has_unconstrained_ty_var`
    /// if we're currently in a bivariant context.
    fn next_ty_var_for_alias(&mut self) -> Ty {
        self.has_unconstrained_ty_var |= self.ambient_variance == Variance::Bivariant;
        self.infcx.next_ty_var_in_universe(self.span, self.for_universe)
    }

    /// An occurs check failure inside of an alias does not mean
    /// that the types definitely don't unify. We may be able
    /// to normalize the alias after all.
    ///
    /// We handle this by lazily equating the alias and generalizing
    /// it to an inference variable. In the new solver, we always
    /// generalize to an infer var unless the alias contains escaping
    /// bound variables.
    ///
    /// Correctly handling aliases with escaping bound variables is
    /// difficult and currently incomplete in two opposite ways:
    /// - if we get an occurs check failure in the alias, replace it with a new infer var.
    ///   This causes us to later emit an alias-relate goal and is incomplete in case the
    ///   alias normalizes to type containing one of the bound variables.
    /// - if the alias contains an inference variable not nameable by `for_universe`, we
    ///   continue generalizing the alias. This ends up pulling down the universe of the
    ///   inference variable and is incomplete in case the alias would normalize to a type
    ///   which does not mention that inference variable.
    fn generalize_alias_ty(
        &mut self,
        alias: AliasTy,
    ) -> Result<Ty, TypeError<DbInterner>> {
        // We do not eagerly replace aliases with inference variables if they have
        // escaping bound vars, see the method comment for details. However, when we
        // are inside of an alias with escaping bound vars replacing nested aliases
        // with inference variables can cause incorrect ambiguity.
        //
        // cc trait-system-refactor-initiative#110
        if self.infcx.next_trait_solver() && !alias.has_escaping_bound_vars() && !self.in_alias {
            return Ok(self.next_ty_var_for_alias());
        }

        let is_nested_alias = mem::replace(&mut self.in_alias, true);
        let result = match self.relate(alias.clone(), alias.clone()) {
            Ok(alias) => Ok(alias.to_ty(self.cx())),
            Err(e) => {
                if is_nested_alias {
                    return Err(e);
                } else {
                    let mut visitor = MaxUniverse::new();
                    alias.visit_with(&mut visitor);
                    let infer_replacement_is_complete =
                        self.for_universe.can_name(visitor.max_universe())
                            && !alias.has_escaping_bound_vars();
                    if !infer_replacement_is_complete {
                        warn!("may incompletely handle alias type: {alias:?}");
                    }

                    debug!("generalization failure in alias");
                    Ok(self.next_ty_var_for_alias())
                }
            }
        };
        self.in_alias = is_nested_alias;
        result
    }
}

impl<'db> TypeRelation for Generalizer<'_, 'db> {
    type I = DbInterner;
    type Ir = DbIr<'db>;
    fn cx(&self) -> DbIr<'db> {
        self.infcx.ir
    }

    fn relate_item_args(
        &mut self,
        item_def_id: GenericDefId,
        a_arg: GenericArgs,
        b_arg: GenericArgs,
    ) -> RelateResult<GenericArgs> {
        if self.ambient_variance == Variance::Invariant {
            // Avoid fetching the variance if we are in an invariant
            // context; no need, and it can induce dependency cycles
            // (e.g., #41849).
            relate::relate_args_invariantly(self, a_arg, b_arg)
        } else {
            let tcx = self.cx();
            let opt_variances = tcx.variances_of(item_def_id);
            relate::relate_args_with_variances(
                self,
                item_def_id,
                opt_variances,
                a_arg,
                b_arg,
                false,
            )
        }
    }

    #[instrument(level = "debug", skip(self, variance, b), ret)]
    fn relate_with_variance<T: Relate<DbInterner>>(
        &mut self,
        variance: Variance,
        _info: VarianceDiagInfo<DbInterner>,
        a: T,
        b: T,
    ) -> RelateResult<T> {
        let old_ambient_variance = self.ambient_variance;
        self.ambient_variance = self.ambient_variance.xform(variance);
        debug!(?self.ambient_variance, "new ambient variance");
        // Recursive calls to `relate` can overflow the stack. For example a deeper version of
        // `ui/associated-consts/issue-93775.rs`.
        let r = self.relate(a, b);
        self.ambient_variance = old_ambient_variance;
        r
    }

    #[instrument(level = "debug", skip(self, t2), ret)]
    fn tys(&mut self, t: Ty, t2: Ty) -> RelateResult<Ty> {
        assert_eq!(t, t2); // we are misusing TypeRelation here; both LHS and RHS ought to be ==

        if let Some(result) = self.cache.get(&(t.clone(), self.ambient_variance, self.in_alias)) {
            return Ok(result.clone());
        }

        // Check to see whether the type we are generalizing references
        // any other type variable related to `vid` via
        // subtyping. This is basically our "occurs check", preventing
        // us from creating infinitely sized types.
        let g = match t.clone().kind() {
            TyKind::Infer(InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_)) => {
                panic!("unexpected infer type: {t:?}")
            }

            TyKind::Infer(InferTy::TyVar(vid)) => {
                let mut inner = self.infcx.inner.borrow_mut();
                let vid = inner.type_variables().root_var(vid);
                if TermVid::Ty(vid) == self.root_vid {
                    // If sub-roots are equal, then `root_vid` and
                    // `vid` are related via subtyping.
                    Err(self.cyclic_term_error())
                } else {
                    let probe = inner.type_variables().probe(vid);
                    match probe {
                        TypeVariableValue::Known { value: u } => {
                            drop(inner);
                            self.relate(u.clone(), u)
                        }
                        TypeVariableValue::Unknown { universe } => {
                            match self.ambient_variance {
                                // Invariant: no need to make a fresh type variable
                                // if we can name the universe.
                                Variance::Invariant => {
                                    if self.for_universe.can_name(universe) {
                                        return Ok(t);
                                    }
                                }

                                // Bivariant: make a fresh var, but remember that
                                // it is unconstrained. See the comment in
                                // `Generalization`.
                                Variance::Bivariant => self.has_unconstrained_ty_var = true,

                                // Co/contravariant: this will be
                                // sufficiently constrained later on.
                                Variance::Covariant | Variance::Contravariant => (),
                            }

                            let origin = inner.type_variables().var_origin(vid);
                            let new_var_id =
                                inner.type_variables().new_var(self.for_universe, origin);
                            // If we're in the new solver and create a new inference
                            // variable inside of an alias we eagerly constrain that
                            // inference variable to prevent unexpected ambiguity errors.
                            //
                            // This is incomplete as it pulls down the universe of the
                            // original inference variable, even though the alias could
                            // normalize to a type which does not refer to that type at
                            // all. I don't expect this to cause unexpected errors in
                            // practice.
                            //
                            // We only need to do so for type and const variables, as
                            // region variables do not impact normalization, and will get
                            // correctly constrained by `AliasRelate` later on.
                            //
                            // cc trait-system-refactor-initiative#108
                            if self.infcx.next_trait_solver()
                                && !matches!(
                                    self.infcx.typing_mode_unchecked(),
                                    TypingMode::Coherence
                                )
                                && self.in_alias
                            {
                                inner.type_variables().equate(vid, new_var_id);
                            }

                            debug!("replacing original vid={:?} with new={:?}", vid, new_var_id);
                            Ok(Ty::new_var(DbInterner, new_var_id))
                        }
                    }
                }
            }

            TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => {
                // No matter what mode we are in,
                // integer/floating-point types must be equal to be
                // relatable.
                Ok(t.clone())
            }

            TyKind::Placeholder(placeholder) => {
                if self.for_universe.can_name(placeholder.universe) {
                    Ok(t.clone())
                } else {
                    debug!(
                        "root universe {:?} cannot name placeholder in universe {:?}",
                        self.for_universe, placeholder.universe
                    );
                    Err(TypeError::Mismatch)
                }
            }

            TyKind::Alias(_, data) => match self.structurally_relate_aliases {
                StructurallyRelateAliases::No => self.generalize_alias_ty(data),
                StructurallyRelateAliases::Yes => relate::structurally_relate_tys(self, t.clone(), t.clone()),
            },

            _ => relate::structurally_relate_tys(self, t.clone(), t.clone()),
        }?;

        self.cache.insert((t, self.ambient_variance, self.in_alias), g.clone());
        Ok(g)
    }

    #[instrument(level = "debug", skip(self, r2), ret)]
    fn regions(
        &mut self,
        r: Region,
        r2: Region,
    ) -> RelateResult<Region> {
        assert_eq!(r, r2); // we are misusing TypeRelation here; both LHS and RHS ought to be ==

        match r.clone().kind() {
            // Never make variables for regions bound within the type itself,
            // nor for erased regions.
            RegionKind::ReBound(..) | RegionKind::ReErased => {
                return Ok(r);
            }

            // It doesn't really matter for correctness if we generalize ReError,
            // since we're already on a doomed compilation path.
            RegionKind::ReError(_) => {
                return Ok(r);
            }

            RegionKind::RePlaceholder(..)
            | RegionKind::ReVar(..)
            | RegionKind::ReStatic
            | RegionKind::ReEarlyParam(..)
            | RegionKind::ReLateParam(..) => {
                // see common code below
            }
        }

        // If we are in an invariant context, we can re-use the region
        // as is, unless it happens to be in some universe that we
        // can't name.
        if let Variance::Invariant = self.ambient_variance {
            let r_universe = self.infcx.universe_of_region(r.clone());
            if self.for_universe.can_name(r_universe) {
                return Ok(r);
            }
        }

        Ok(self.infcx.next_region_var_in_universe(
            RegionVariableOrigin::MiscVariable(self.span),
            self.for_universe,
        ))
    }

    #[instrument(level = "debug", skip(self, c2), ret)]
    fn consts(
        &mut self,
        c: Const,
        c2: Const,
    ) -> RelateResult<Const> {
        assert_eq!(c, c2); // we are misusing TypeRelation here; both LHS and RHS ought to be ==

        match c.clone().kind() {
            ConstKind::Infer(InferConst::Var(vid)) => {
                // If root const vids are equal, then `root_vid` and
                // `vid` are related and we'd be inferring an infinitely
                // deep const.
                if TermVid::Const(
                    self.infcx.inner.borrow_mut().const_unification_table().find(vid).vid,
                ) == self.root_vid
                {
                    return Err(self.cyclic_term_error());
                }

                let mut inner = self.infcx.inner.borrow_mut();
                let variable_table = &mut inner.const_unification_table();
                match variable_table.probe_value(vid) {
                    ConstVariableValue::Known { value: u } => {
                        drop(inner);
                        self.relate(u.clone(), u)
                    }
                    ConstVariableValue::Unknown { origin, universe } => {
                        if self.for_universe.can_name(universe) {
                            Ok(c)
                        } else {
                            let new_var_id = variable_table
                                .new_key(ConstVariableValue::Unknown {
                                    origin,
                                    universe: self.for_universe,
                                })
                                .vid;

                            // See the comment for type inference variables
                            // for more details.
                            if self.infcx.next_trait_solver()
                                && !matches!(
                                    self.infcx.typing_mode_unchecked(),
                                    TypingMode::Coherence
                                )
                                && self.in_alias
                            {
                                variable_table.union(vid, new_var_id);
                            }
                            Ok(Const::new_var(DbInterner, new_var_id))
                        }
                    }
                }
            }
            // FIXME: Unevaluated constants are also not rigid, so the current
            // approach of always relating them structurally is incomplete.
            //
            // FIXME: remove this branch once `structurally_relate_consts` is fully
            // structural.
            ConstKind::Unevaluated(UnevaluatedConst { def, args }) => {
                let args = self.relate_with_variance(
                    Variance::Invariant,
                    VarianceDiagInfo::default(),
                    args.clone(),
                    args,
                )?;
                Ok(Const::new_unevaluated(DbInterner, UnevaluatedConst { def, args }))
            }
            ConstKind::Placeholder(placeholder) => {
                if self.for_universe.can_name(placeholder.universe) {
                    Ok(c)
                } else {
                    debug!(
                        "root universe {:?} cannot name placeholder in universe {:?}",
                        self.for_universe, placeholder.universe
                    );
                    Err(TypeError::Mismatch)
                }
            }
            _ => relate::structurally_relate_consts(self, c.clone(), c),
        }
    }

    #[instrument(level = "debug", skip(self), ret)]
    fn binders<T>(
        &mut self,
        a: Binder<T>,
        _: Binder<T>,
    ) -> RelateResult<Binder<T>>
    where
        T: Relate<DbInterner>,
    {
        let result = self.relate(a.clone().skip_binder(), a.clone().skip_binder())?;
        Ok(a.rebind(result))
    }
}

/// Result from a generalization operation. This includes
/// not only the generalized type, but also a bool flag
/// indicating whether further WF checks are needed.
#[derive(Debug)]
struct Generalization<T> {
    /// When generalizing `<?0 as Trait>::Assoc` or
    /// `<T as Bar<<?0 as Foo>::Assoc>>::Assoc`
    /// for `?0` generalization returns an inference
    /// variable.
    ///
    /// This has to be handled wotj care as it can
    /// otherwise very easily result in infinite
    /// recursion.
    pub value_may_be_infer: T,

    /// In general, we do not check whether all types which occur during
    /// type checking are well-formed. We only check wf of user-provided types
    /// and when actually using a type, e.g. for method calls.
    ///
    /// This means that when subtyping, we may end up with unconstrained
    /// inference variables if a generalized type has bivariant parameters.
    /// A parameter may only be bivariant if it is constrained by a projection
    /// bound in a where-clause. As an example, imagine a type:
    ///
    ///     struct Foo<A, B> where A: Iterator<Item = B> {
    ///         data: A
    ///     }
    ///
    /// here, `A` will be covariant, but `B` is unconstrained.
    ///
    /// However, whatever it is, for `Foo` to be WF, it must be equal to `A::Item`.
    /// If we have an input `Foo<?A, ?B>`, then after generalization we will wind
    /// up with a type like `Foo<?C, ?D>`. When we enforce `Foo<?A, ?B> <: Foo<?C, ?D>`,
    /// we will wind up with the requirement that `?A <: ?C`, but no particular
    /// relationship between `?B` and `?D` (after all, these types may be completely
    /// different). If we do nothing else, this may mean that `?D` goes unconstrained
    /// (as in #41677). To avoid this we emit a `WellFormed` obligation in these cases.
    pub has_unconstrained_ty_var: bool,
}
