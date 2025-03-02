//! # Lattice variables
//!
//! Generic code for operating on [lattices] of inference variables
//! that are characterized by an upper- and lower-bound.
//!
//! The code is defined quite generically so that it can be
//! applied both to type variables, which represent types being inferred,
//! and fn variables, which represent function types being inferred.
//! (It may eventually be applied to their types as well.)
//! In some cases, the functions are also generic with respect to the
//! operation on the lattice (GLB vs LUB).
//!
//! ## Note
//!
//! Although all the functions are generic, for simplicity, comments in the source code
//! generally refer to type variables and the LUB operation.
//!
//! [lattices]: https://en.wikipedia.org/wiki/Lattice_(order)

use rustc_type_ir::{inherent::{DefId, IntoKind}, relate::{combine::{super_combine_consts, super_combine_tys}, Relate, TypeRelation, VarianceDiagInfo}, AliasRelationDirection, AliasTyKind, InferCtxtLike, InferTy, Upcast, Variance};
use rustc_type_ir::visit::TypeVisitableExt;
use tracing::{debug, instrument};

use super::{RelateResult, StructurallyRelateAliases};
use super::combine::PredicateEmittingRelation;
use crate::next_solver::{infer::{traits::{Obligation, PredicateObligations}, DefineOpaqueTypes, InferCtxt, SubregionOrigin, TypeTrace}, AliasTy, Binder, Const, DbInterner, DbIr, Goal, ParamEnv, Predicate, PredicateKind, Region, Span, Ty, TyKind};

#[derive(Clone, Copy)]
pub(crate) enum LatticeOpKind {
    Glb,
    Lub,
}

impl LatticeOpKind {
    fn invert(self) -> Self {
        match self {
            LatticeOpKind::Glb => LatticeOpKind::Lub,
            LatticeOpKind::Lub => LatticeOpKind::Glb,
        }
    }
}

/// A greatest lower bound" (common subtype) or least upper bound (common supertype).
pub(crate) struct LatticeOp<'infcx, 'db> {
    infcx: &'infcx InferCtxt<'db>,
    // Immutable fields
    trace: TypeTrace,
    param_env: ParamEnv,
    // Mutable fields
    kind: LatticeOpKind,
    obligations: PredicateObligations,
}

impl<'infcx, 'db> LatticeOp<'infcx, 'db> {
    pub(crate) fn new(
        infcx: &'infcx InferCtxt<'db>,
        trace: TypeTrace,
        param_env: ParamEnv,
        kind: LatticeOpKind,
    ) -> LatticeOp<'infcx, 'db> {
        LatticeOp { infcx, trace, param_env, kind, obligations: PredicateObligations::new() }
    }

    pub(crate) fn into_obligations(self) -> PredicateObligations {
        self.obligations
    }
}

impl<'db> TypeRelation for LatticeOp<'_, 'db> {
    type I = DbInterner;
    type Ir = DbIr<'db>;
    fn cx(&self) -> DbIr<'db> {
        self.infcx.ir
    }

    fn relate_with_variance<T: Relate<DbInterner>>(
        &mut self,
        variance: Variance,
        _info: VarianceDiagInfo<DbInterner>,
        a: T,
        b: T,
    ) -> RelateResult<T> {
        match variance {
            Variance::Invariant => {
                self.obligations.extend(
                    self.infcx
                        .at(&self.trace.cause, self.param_env.clone())
                        .eq_trace(DefineOpaqueTypes::Yes, self.trace.clone(), a.clone(), b)?
                        .into_obligations(),
                );
                Ok(a)
            }
            Variance::Covariant => self.relate(a, b),
            // FIXME(#41044) -- not correct, need test
            Variance::Bivariant => Ok(a),
            Variance::Contravariant => {
                self.kind = self.kind.invert();
                let res = self.relate(a, b);
                self.kind = self.kind.invert();
                res
            }
        }
    }

    /// Relates two types using a given lattice.
    #[instrument(skip(self), level = "trace")]
    fn tys(&mut self, a: Ty, b: Ty) -> RelateResult<Ty> {
        if a == b {
            return Ok(a);
        }

        let infcx = self.infcx;

        let a = infcx.shallow_resolve(a);
        let b = infcx.shallow_resolve(b);

        match (a.clone().kind(), b.clone().kind()) {
            // If one side is known to be a variable and one is not,
            // create a variable (`v`) to represent the LUB. Make sure to
            // relate `v` to the non-type-variable first (by passing it
            // first to `relate_bound`). Otherwise, we would produce a
            // subtype obligation that must then be processed.
            //
            // Example: if the LHS is a type variable, and RHS is
            // `Box<i32>`, then we current compare `v` to the RHS first,
            // which will instantiate `v` with `Box<i32>`. Then when `v`
            // is compared to the LHS, we instantiate LHS with `Box<i32>`.
            // But if we did in reverse order, we would create a `v <:
            // LHS` (or vice versa) constraint and then instantiate
            // `v`. This would require further processing to achieve same
            // end-result; in particular, this screws up some of the logic
            // in coercion, which expects LUB to figure out that the LHS
            // is (e.g.) `Box<i32>`. A more obvious solution might be to
            // iterate on the subtype obligations that are returned, but I
            // think this suffices. -nmatsakis
            (TyKind::Infer(InferTy::TyVar(..)), _) => {
                let v = infcx.next_ty_var(self.trace.cause.span);
                self.relate_bound(v.clone(), b, a)?;
                Ok(v)
            }
            (_, TyKind::Infer(InferTy::TyVar(..))) => {
                let v = infcx.next_ty_var(self.trace.cause.span);
                self.relate_bound(v.clone(), a, b)?;
                Ok(v)
            }

            (
                TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id: a_def_id, .. }),
                TyKind::Alias(AliasTyKind::Opaque, AliasTy { def_id: b_def_id, .. }),
            ) if a_def_id == b_def_id => super_combine_tys(infcx, self, a, b),

            _ => super_combine_tys(infcx, self, a, b),
        }
    }

    #[instrument(skip(self), level = "trace")]
    fn regions(
        &mut self,
        a: Region,
        b: Region,
    ) -> RelateResult<Region> {
        let origin = SubregionOrigin::Subtype(Box::new(self.trace.clone()));
        let mut inner = self.infcx.inner.borrow_mut();
        let mut constraints = inner.unwrap_region_constraints();
        Ok(match self.kind {
            // GLB(&'static u8, &'a u8) == &RegionLUB('static, 'a) u8 == &'static u8
            LatticeOpKind::Glb => constraints.lub_regions(self.cx(), origin, a, b),

            // LUB(&'static u8, &'a u8) == &RegionGLB('static, 'a) u8 == &'a u8
            LatticeOpKind::Lub => constraints.glb_regions(self.cx(), origin, a, b),
        })
    }

    #[instrument(skip(self), level = "trace")]
    fn consts(
        &mut self,
        a: Const,
        b: Const,
    ) -> RelateResult<Const> {
        super_combine_consts(self.infcx, self, a, b)
    }

    fn binders<T>(
        &mut self,
        a: Binder<T>,
        b: Binder<T>,
    ) -> RelateResult<Binder<T>>
    where
        T: Relate<DbInterner>,
    {
        // GLB/LUB of a binder and itself is just itself
        if a == b {
            return Ok(a);
        }

        debug!("binders(a={:?}, b={:?})", a, b);
        if a.clone().skip_binder().has_escaping_bound_vars()
            || b.clone().skip_binder().has_escaping_bound_vars()
        {
            // When higher-ranked types are involved, computing the GLB/LUB is
            // very challenging, switch to invariance. This is obviously
            // overly conservative but works ok in practice.
            self.relate_with_variance(
                Variance::Invariant,
                VarianceDiagInfo::default(),
                a.clone(),
                b,
            )?;
            Ok(a)
        } else {
            Ok(Binder::dummy(self.relate(a.skip_binder(), b.skip_binder())?))
        }
    }
}

impl LatticeOp<'_, '_> {
    // Relates the type `v` to `a` and `b` such that `v` represents
    // the LUB/GLB of `a` and `b` as appropriate.
    //
    // Subtle hack: ordering *may* be significant here. This method
    // relates `v` to `a` first, which may help us to avoid unnecessary
    // type variable obligations. See caller for details.
    fn relate_bound(&mut self, v: Ty, a: Ty, b: Ty) -> RelateResult<()> {
        let at = self.infcx.at(&self.trace.cause, self.param_env.clone());
        match self.kind {
            LatticeOpKind::Glb => {
                self.obligations.extend(at.clone().sub(DefineOpaqueTypes::Yes, v.clone(), a)?.into_obligations());
                self.obligations.extend(at.sub(DefineOpaqueTypes::Yes, v, b)?.into_obligations());
            }
            LatticeOpKind::Lub => {
                self.obligations.extend(at.clone().sub(DefineOpaqueTypes::Yes, a, v.clone())?.into_obligations());
                self.obligations.extend(at.sub(DefineOpaqueTypes::Yes, b, v)?.into_obligations());
            }
        }
        Ok(())
    }
}

impl<'db> PredicateEmittingRelation<InferCtxt<'db>> for LatticeOp<'_, 'db> {
    fn span(&self) -> Span {
        self.trace.span()
    }

    fn structurally_relate_aliases(&self) -> StructurallyRelateAliases {
        StructurallyRelateAliases::No
    }

    fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }

    fn register_predicates(
        &mut self,
        preds: impl IntoIterator<Item: Upcast<DbInterner, Predicate>>,
    ) {
        self.obligations.extend(preds.into_iter().map(|pred| {
            Obligation::new(DbInterner, self.trace.cause.clone(), self.param_env.clone(), pred)
        }))
    }

    fn register_goals(&mut self, goals: impl IntoIterator<Item = Goal<Predicate>>) {
        self.obligations.extend(goals.into_iter().map(|goal| {
            Obligation::new(
                DbInterner,
                self.trace.cause.clone(),
                goal.param_env,
                goal.predicate,
            )
        }))
    }

    fn register_alias_relate_predicate(&mut self, a: Ty, b: Ty) {
        self.register_predicates([Binder::dummy(PredicateKind::AliasRelate(
            a.into(),
            b.into(),
            // FIXME(deferred_projection_equality): This isn't right, I think?
            AliasRelationDirection::Equate,
        ))]);
    }
}
