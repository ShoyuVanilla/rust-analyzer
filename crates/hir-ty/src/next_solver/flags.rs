use std::slice;

use rustc_type_ir::{
    inherent::{GenericArgs as _, IntoKind, SliceLike},
    visit::Flags,
    AliasTy, CoercePredicate, DebruijnIndex, ExistentialPredicate, GenericArgKind,
    HostEffectPredicate, InferConst, NormalizesTo, OutlivesPredicate, ProjectionPredicate,
    RegionKind::ReBound,
    SubtypePredicate, TermKind, TypeFlags,
};

use super::{
    AliasTerm, Binder, Clause, ClauseKind, Const, ConstKind, DbInterner, ExistentialProjection,
    GenericArg, GenericArgs, PredicateKind, Region, Term, Ty, TyKind, Tys,
};

#[derive(Debug)]
pub struct FlagComputation {
    pub flags: TypeFlags,

    /// see `outer_exclusive_binder` for details
    pub outer_exclusive_binder: DebruijnIndex,
}

impl FlagComputation {
    fn new() -> FlagComputation {
        FlagComputation { flags: TypeFlags::empty(), outer_exclusive_binder: DebruijnIndex::ZERO }
    }

    #[allow(rustc::usage_of_ty_tykind)]
    pub fn for_kind(kind: &TyKind) -> FlagComputation {
        let mut result = FlagComputation::new();
        result.add_kind(kind);
        result
    }

    pub fn for_predicate(binder: Binder<PredicateKind>) -> FlagComputation {
        let mut result = FlagComputation::new();
        result.add_predicate(binder);
        result
    }

    pub fn for_const_kind(kind: &ConstKind) -> FlagComputation {
        let mut result = FlagComputation::new();
        result.add_const_kind(kind);
        result
    }

    pub fn for_clauses(clauses: &[Clause]) -> FlagComputation {
        let mut result = FlagComputation::new();
        for c in clauses {
            result.add_flags(c.clone().as_predicate().flags());
            result.add_exclusive_binder(c.clone().as_predicate().outer_exclusive_binder());
        }
        result
    }

    fn add_flags(&mut self, flags: TypeFlags) {
        self.flags |= flags;
    }

    /// indicates that `self` refers to something at binding level `binder`
    fn add_bound_var(&mut self, binder: DebruijnIndex) {
        let exclusive_binder = binder.shifted_in(1);
        self.add_exclusive_binder(exclusive_binder);
    }

    /// indicates that `self` refers to something *inside* binding
    /// level `binder` -- not bound by `binder`, but bound by the next
    /// binder internal to it
    fn add_exclusive_binder(&mut self, exclusive_binder: DebruijnIndex) {
        self.outer_exclusive_binder = self.outer_exclusive_binder.max(exclusive_binder);
    }

    /// Adds the flags/depth from a set of types that appear within the current type, but within a
    /// region binder.
    fn bound_computation<T, F>(&mut self, value: Binder<T>, f: F)
    where
        F: FnOnce(&mut Self, T),
    {
        let mut computation = FlagComputation::new();

        if !value.bound_vars().is_empty() {
            computation.add_flags(TypeFlags::HAS_BINDER_VARS);
        }

        f(&mut computation, value.skip_binder());

        self.add_flags(computation.flags);

        // The types that contributed to `computation` occurred within
        // a region binder, so subtract one from the region depth
        // within when adding the depth to `self`.
        let outer_exclusive_binder = computation.outer_exclusive_binder;
        if outer_exclusive_binder > DebruijnIndex::ZERO {
            self.add_exclusive_binder(outer_exclusive_binder.shifted_out(1));
        } // otherwise, this binder captures nothing
    }

    #[allow(rustc::usage_of_ty_tykind)]
    fn add_kind(&mut self, kind: &TyKind) {
        use rustc_type_ir::AliasTyKind::*;
        use rustc_type_ir::InferTy::*;
        use rustc_type_ir::TyKind::*;
        match kind.clone() {
            Bool | Char | Int(_) | Float(_) | Uint(_) | Never | Str | Foreign(..) => {}

            Error(_) => self.add_flags(TypeFlags::HAS_ERROR),

            Param(_) => {
                self.add_flags(TypeFlags::HAS_TY_PARAM);
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
            }

            Coroutine(_, args) => {
                let args = args.clone().as_coroutine();
                let should_remove_further_specializable =
                    !self.flags.contains(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                self.add_args(args.clone().parent_args().as_slice());
                if should_remove_further_specializable {
                    self.flags -= TypeFlags::STILL_FURTHER_SPECIALIZABLE;
                }

                self.add_ty(&args.clone().resume_ty());
                self.add_ty(&args.clone().return_ty());
                self.add_ty(&args.clone().witness());
                self.add_ty(&args.clone().yield_ty());
                self.add_ty(&args.clone().tupled_upvars_ty());
            }

            CoroutineWitness(_, args) => {
                let should_remove_further_specializable =
                    !self.flags.contains(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                self.add_args(args.as_slice());
                if should_remove_further_specializable {
                    self.flags -= TypeFlags::STILL_FURTHER_SPECIALIZABLE;
                }
                self.add_flags(TypeFlags::HAS_TY_COROUTINE);
            }

            Closure(_, args) => {
                let args = args.as_closure();
                let should_remove_further_specializable =
                    !self.flags.contains(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                self.add_args(args.clone().parent_args().as_slice());
                if should_remove_further_specializable {
                    self.flags -= TypeFlags::STILL_FURTHER_SPECIALIZABLE;
                }

                self.add_ty(&args.clone().sig_as_fn_ptr_ty());
                self.add_ty(&args.clone().kind_ty());
                self.add_ty(&args.clone().tupled_upvars_ty());
            }

            CoroutineClosure(_, args) => {
                let args = args.as_coroutine_closure();
                let should_remove_further_specializable =
                    !self.flags.contains(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                self.add_args(args.clone().parent_args().as_slice());
                if should_remove_further_specializable {
                    self.flags -= TypeFlags::STILL_FURTHER_SPECIALIZABLE;
                }

                self.add_ty(&args.clone().kind_ty());
                self.add_ty(&args.clone().signature_parts_ty());
                self.add_ty(&args.clone().tupled_upvars_ty());
                self.add_ty(&args.clone().coroutine_captures_by_ref_ty());
                self.add_ty(&args.clone().coroutine_witness_ty());
            }

            Bound(debruijn, _) => {
                self.add_bound_var(debruijn);
                self.add_flags(TypeFlags::HAS_TY_BOUND);
            }

            Placeholder(..) => {
                self.add_flags(TypeFlags::HAS_TY_PLACEHOLDER);
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
            }

            Infer(infer) => {
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                match infer {
                    FreshTy(_) | FreshIntTy(_) | FreshFloatTy(_) => {
                        self.add_flags(TypeFlags::HAS_TY_FRESH)
                    }

                    TyVar(_) | IntVar(_) | FloatVar(_) => self.add_flags(TypeFlags::HAS_TY_INFER),
                }
            }

            Adt(_, args) => {
                self.add_args(args.as_slice());
            }

            Alias(kind, data) => {
                self.add_flags(match kind {
                    Projection => TypeFlags::HAS_TY_PROJECTION,
                    Weak => TypeFlags::HAS_TY_WEAK,
                    Opaque => TypeFlags::HAS_TY_OPAQUE,
                    Inherent => TypeFlags::HAS_TY_INHERENT,
                });

                self.add_alias_ty(data);
            }

            Dynamic(obj, r, _) => {
                for predicate in obj.iter() {
                    self.bound_computation(predicate, |computation, predicate| match predicate {
                        ExistentialPredicate::Trait(tr) => computation.add_args(tr.args.as_slice()),
                        ExistentialPredicate::Projection(p) => {
                            computation.add_existential_projection(&p);
                        }
                        ExistentialPredicate::AutoTrait(_) => {}
                    });
                }

                self.add_region(r);
            }

            Array(tt, len) => {
                self.add_ty(&tt);
                self.add_const(len);
            }

            Pat(ty, pat) => {
                self.add_ty(&ty);
                todo!()
            }

            Slice(tt) => self.add_ty(&tt),

            RawPtr(ty, _) => {
                self.add_ty(&ty);
            }

            Ref(r, ty, _) => {
                self.add_region(r);
                self.add_ty(&ty);
            }

            Tuple(types) => {
                self.add_tys(types);
            }

            FnDef(_, args) => {
                self.add_args(args.as_slice());
            }

            FnPtr(sig_tys, _) => self.bound_computation(sig_tys, |computation, sig_tys| {
                computation.add_tys(sig_tys.inputs_and_output);
            }),
        }
    }

    fn add_predicate(&mut self, binder: Binder<PredicateKind>) {
        self.bound_computation(binder, |computation, atom| computation.add_predicate_atom(atom));
    }

    fn add_predicate_atom(&mut self, atom: PredicateKind) {
        match atom {
            PredicateKind::Clause(ClauseKind::Trait(trait_pred)) => {
                self.add_args(trait_pred.trait_ref.args.as_slice());
            }
            PredicateKind::Clause(ClauseKind::HostEffect(HostEffectPredicate {
                trait_ref,
                constness: _,
            })) => {
                self.add_args(trait_ref.args.as_slice());
            }
            PredicateKind::Clause(ClauseKind::RegionOutlives(OutlivesPredicate(a, b))) => {
                self.add_region(a);
                self.add_region(b);
            }
            PredicateKind::Clause(ClauseKind::TypeOutlives(OutlivesPredicate(ty, region))) => {
                self.add_ty(&ty);
                self.add_region(region);
            }
            PredicateKind::Clause(ClauseKind::ConstArgHasType(ct, ty)) => {
                self.add_const(ct);
                self.add_ty(&ty);
            }
            PredicateKind::Subtype(SubtypePredicate { a_is_expected: _, a, b }) => {
                self.add_ty(&a);
                self.add_ty(&b);
            }
            PredicateKind::Coerce(CoercePredicate { a, b }) => {
                self.add_ty(&a);
                self.add_ty(&b);
            }
            PredicateKind::Clause(ClauseKind::Projection(ProjectionPredicate {
                projection_term,
                term,
            })) => {
                self.add_alias_term(projection_term);
                self.add_term(term);
            }
            PredicateKind::Clause(ClauseKind::WellFormed(arg)) => {
                self.add_args(slice::from_ref(&arg));
            }
            PredicateKind::DynCompatible(_def_id) => {}
            PredicateKind::Clause(ClauseKind::ConstEvaluatable(uv)) => {
                self.add_const(uv);
            }
            PredicateKind::ConstEquate(expected, found) => {
                self.add_const(expected);
                self.add_const(found);
            }
            PredicateKind::Ambiguous => {}
            PredicateKind::NormalizesTo(NormalizesTo { alias, term }) => {
                self.add_alias_term(alias);
                self.add_term(term);
            }
            PredicateKind::AliasRelate(t1, t2, _) => {
                self.add_term(t1);
                self.add_term(t2);
            }
        }
    }

    fn add_ty(&mut self, ty: &Ty) {
        self.add_flags(ty.flags());
        self.add_exclusive_binder(ty.outer_exclusive_binder());
    }

    fn add_tys(&mut self, tys: Tys) {
        for ty in tys.as_slice() {
            self.add_ty(ty);
        }
    }

    fn add_region(&mut self, r: Region) {
        self.add_flags(r.type_flags());
        if let ReBound(debruijn, _) = r.clone().kind() {
            self.add_bound_var(debruijn);
        }
    }

    fn add_const(&mut self, c: Const) {
        self.add_flags(c.flags());
        self.add_exclusive_binder(c.outer_exclusive_binder());
    }

    fn add_const_kind(&mut self, c: &ConstKind) {
        match c {
            ConstKind::Unevaluated(uv) => {
                self.add_args(uv.args.as_slice());
                self.add_flags(TypeFlags::HAS_CT_PROJECTION);
            }
            ConstKind::Infer(infer) => {
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
                match infer {
                    InferConst::Fresh(_) => self.add_flags(TypeFlags::HAS_CT_FRESH),
                    InferConst::Var(_) => self.add_flags(TypeFlags::HAS_CT_INFER),
                }
            }
            ConstKind::Bound(debruijn, _) => {
                self.add_bound_var(*debruijn);
                self.add_flags(TypeFlags::HAS_CT_BOUND);
            }
            ConstKind::Param(_) => {
                self.add_flags(TypeFlags::HAS_CT_PARAM);
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
            }
            ConstKind::Placeholder(_) => {
                self.add_flags(TypeFlags::HAS_CT_PLACEHOLDER);
                self.add_flags(TypeFlags::STILL_FURTHER_SPECIALIZABLE);
            }
            ConstKind::Value(ty, _) => self.add_ty(ty),
            ConstKind::Expr(e) => todo!(),
            ConstKind::Error(_) => self.add_flags(TypeFlags::HAS_ERROR),
        }
    }

    fn add_existential_projection(&mut self, projection: &ExistentialProjection) {
        self.add_args(projection.args.as_slice());
        match projection.term.clone().kind() {
            TermKind::Ty(ty) => self.add_ty(&ty),
            TermKind::Const(ct) => self.add_const(ct),
        }
    }

    fn add_alias_ty(&mut self, alias_ty: AliasTy<DbInterner>) {
        self.add_args(alias_ty.args.as_slice());
    }

    fn add_alias_term(&mut self, alias_term: AliasTerm) {
        self.add_args(alias_term.args.as_slice());
    }

    fn add_args(&mut self, args: &[GenericArg]) {
        for arg in args {
            match arg.clone().kind() {
                GenericArgKind::Type(ty) => self.add_ty(&ty),
                GenericArgKind::Lifetime(lt) => self.add_region(lt),
                GenericArgKind::Const(ct) => self.add_const(ct),
            }
        }
    }

    fn add_term(&mut self, term: Term) {
        match term.kind() {
            TermKind::Ty(ty) => self.add_ty(&ty),
            TermKind::Const(ct) => self.add_const(ct),
        }
    }
}
