use base_db::ra_salsa::{self, InternKey};
use chalk_ir::{fold::Shift, interner::HasInterner, CanonicalVarKinds};
use hir_def::{CallableDefId, ClosureId, ConstParamId, FunctionId, GenericDefId, LifetimeParamId, TypeAliasId, TypeOrConstParamId, TypeParamId};
use intern::sym;
use rustc_type_ir::{
    elaborate, fold::{shift_vars, TypeFoldable, TypeSuperFoldable}, inherent::{BoundVarLike, Clause as _, IntoKind, PlaceholderLike, SliceLike}, solve::Goal, visit::{TypeVisitable, TypeVisitableExt}, AliasTerm, BoundVar, ExistentialProjection, ExistentialTraitRef, ProjectionPredicate, RustIr, UniverseIndex
};

use crate::{
    db::HirDatabase, from_assoc_type_id, from_chalk_trait_id, mapping::{from_opaque_ty_id, ToChalk}, next_solver::{
        interner::{AdtDef, BoundVarKind, BoundVarKinds, DbInterner},
        Binder, ClauseKind, TraitPredicate,
    }, Interner
};

use super::{
    BoundExistentialPredicate, BoundExistentialPredicates, BoundRegion, BoundRegionKind, BoundTy, BoundTyKind, Canonical, CanonicalVarInfo, CanonicalVars, Clause, Clauses, Const, DbIr, EarlyParamRegion, ErrorGuaranteed, ExistentialPredicate, GenericArg, GenericArgs, ParamConst, ParamEnv, ParamTy, Placeholder, PlaceholderConst, PlaceholderRegion, PlaceholderTy, Predicate, PredicateKind, Region, Term, TraitRef, Ty, Tys, ValueConst, VariancesOf
};

pub fn to_placeholder_idx<T: Clone + std::fmt::Debug>(db: &dyn HirDatabase, id: TypeOrConstParamId, map: impl Fn(BoundVar) -> T) -> Placeholder<T> {
    let interned_id = db.intern_type_or_const_param_id(id);
    Placeholder { 
        universe: UniverseIndex::ZERO,
        bound: map(BoundVar::from_usize(ra_salsa::InternKey::as_intern_id(&interned_id).as_usize()))
    }
}

struct BinderToEarlyBinder {
    debruijn: rustc_type_ir::DebruijnIndex,
}

impl rustc_type_ir::fold::TypeFolder<DbInterner> for BinderToEarlyBinder {
    fn cx(&self) -> DbInterner {
        DbInterner
    }

    fn fold_binder<T>(
        &mut self,
        t: rustc_type_ir::Binder<DbInterner, T>,
    ) -> rustc_type_ir::Binder<DbInterner, T>
    where
        T: TypeFoldable<DbInterner>,
    {
        self.debruijn.shift_in(1);
        let result = t.super_fold_with(self);
        self.debruijn.shift_out(1);
        result
    }

    fn fold_ty(&mut self, t: Ty) -> Ty {
        match t.clone().kind() {
            rustc_type_ir::TyKind::Bound(debruijn, bound_ty) if self.debruijn == debruijn => {
                let var: rustc_type_ir::BoundVar = bound_ty.var();
                Ty::new(rustc_type_ir::TyKind::Param(ParamTy {
                    index: var.as_u32(),
                    name: sym::MISSING_NAME.clone(),
                }))
            }
            _ => t.super_fold_with(self),
        }
    }

    fn fold_region(&mut self, r: Region) -> Region {
        match r.clone().kind() {
            rustc_type_ir::ReBound(debruijn, bound_region) if self.debruijn == debruijn => {
                let var: rustc_type_ir::BoundVar = bound_region.var();
                Region::new(rustc_type_ir::RegionKind::ReEarlyParam(EarlyParamRegion {
                    index: var.as_u32(),
                    name: sym::MISSING_NAME.clone(),
                }))
            }
            _ => r,
        }
    }

    fn fold_const(&mut self, c: Const) -> Const {
        match c.clone().kind() {
            rustc_type_ir::ConstKind::Bound(debruijn, var) if self.debruijn == debruijn => {
                Const::new(rustc_type_ir::ConstKind::Param(ParamConst {
                    index: var.as_u32(),
                    name: sym::MISSING_NAME.clone(),
                }))
            }
            _ => c.super_fold_with(self),
        }
    }
}

pub trait ChalkToNextSolver<Out> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Out;
}

impl ChalkToNextSolver<Ty> for chalk_ir::Ty<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Ty {
        Ty::new(match self.kind(Interner) {
            chalk_ir::TyKind::Adt(adt_id, substitution) => {
                let def = AdtDef::new(adt_id.0, ir.db);
                let args = substitution.to_nextsolver(ir);
                rustc_type_ir::TyKind::Adt(def, args)
            }
            chalk_ir::TyKind::AssociatedType(assoc_type_id, substitution) => {
                let id: TypeAliasId = ra_salsa::InternKey::from_intern_id(assoc_type_id.0);
                let args: GenericArgs = substitution.to_nextsolver(ir);
                let alias_ty = rustc_type_ir::AliasTy::new(ir, id.into(), args.iter());
                rustc_type_ir::TyKind::Alias(rustc_type_ir::AliasTyKind::Opaque, alias_ty)
            }
            chalk_ir::TyKind::Scalar(scalar) => match scalar {
                chalk_ir::Scalar::Bool => rustc_type_ir::TyKind::Bool,
                chalk_ir::Scalar::Char => rustc_type_ir::TyKind::Char,
                chalk_ir::Scalar::Int(chalk_ir::IntTy::Isize) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::Isize)
                }
                chalk_ir::Scalar::Int(chalk_ir::IntTy::I8) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::I8)
                }
                chalk_ir::Scalar::Int(chalk_ir::IntTy::I16) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::I16)
                }
                chalk_ir::Scalar::Int(chalk_ir::IntTy::I32) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::I32)
                }
                chalk_ir::Scalar::Int(chalk_ir::IntTy::I64) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::I64)
                }
                chalk_ir::Scalar::Int(chalk_ir::IntTy::I128) => {
                    rustc_type_ir::TyKind::Int(rustc_type_ir::IntTy::I128)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::Usize) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::Usize)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::U8) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::U8)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::U16) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::U16)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::U32) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::U32)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::U64) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::U64)
                }
                chalk_ir::Scalar::Uint(chalk_ir::UintTy::U128) => {
                    rustc_type_ir::TyKind::Uint(rustc_type_ir::UintTy::U128)
                }
                chalk_ir::Scalar::Float(chalk_ir::FloatTy::F16) => {
                    rustc_type_ir::TyKind::Float(rustc_type_ir::FloatTy::F16)
                }
                chalk_ir::Scalar::Float(chalk_ir::FloatTy::F32) => {
                    rustc_type_ir::TyKind::Float(rustc_type_ir::FloatTy::F32)
                }
                chalk_ir::Scalar::Float(chalk_ir::FloatTy::F64) => {
                    rustc_type_ir::TyKind::Float(rustc_type_ir::FloatTy::F64)
                }
                chalk_ir::Scalar::Float(chalk_ir::FloatTy::F128) => {
                    rustc_type_ir::TyKind::Float(rustc_type_ir::FloatTy::F128)
                }
            },
            chalk_ir::TyKind::Tuple(_, substitution) => {
                let args = substitution.to_nextsolver(ir);
                rustc_type_ir::TyKind::Tuple(args)
            }
            chalk_ir::TyKind::Array(ty, len) => {
                rustc_type_ir::TyKind::Array(ty.to_nextsolver(ir), len.to_nextsolver(ir))
            }
            chalk_ir::TyKind::Slice(ty) => rustc_type_ir::TyKind::Slice(ty.to_nextsolver(ir)),
            chalk_ir::TyKind::Raw(mutability, ty) => {
                rustc_type_ir::RawPtr(ty.to_nextsolver(ir), mutability.to_nextsolver(ir))
            }
            chalk_ir::TyKind::Ref(mutability, lifetime, ty) => rustc_type_ir::TyKind::Ref(
                lifetime.to_nextsolver(ir),
                ty.to_nextsolver(ir),
                mutability.to_nextsolver(ir),
            ),
            chalk_ir::TyKind::OpaqueType(def_id, substitution) => {
                let args: GenericArgs = substitution.to_nextsolver(ir);
                let alias_ty = rustc_type_ir::AliasTy::new(ir, from_opaque_ty_id(*def_id).into(), args);
                rustc_type_ir::TyKind::Alias(rustc_type_ir::AliasTyKind::Opaque, alias_ty)
            }
            chalk_ir::TyKind::FnDef(fn_def_id, substitution) => {
                let def_id = CallableDefId::from_chalk(ir.db, *fn_def_id);
                let id = match def_id {
                    CallableDefId::FunctionId(id) => id,
                    _ => todo!()
                };
                rustc_type_ir::TyKind::FnDef(id.into(), substitution.to_nextsolver(ir))
            }
            chalk_ir::TyKind::Str => rustc_type_ir::TyKind::Str,
            chalk_ir::TyKind::Never => rustc_type_ir::TyKind::Never,
            chalk_ir::TyKind::Closure(closure_id, substitution) => {
                let id: ClosureId = ra_salsa::InternKey::from_intern_id(closure_id.0);
                rustc_type_ir::TyKind::Closure(id.into(), substitution.to_nextsolver(ir))
            }
            chalk_ir::TyKind::Coroutine(_coroutine_id, _substitution) => {
                //let id = ra_salsa::InternKey::from_intern_id(coroutine_id.0);
                //rustc_type_ir::TyKind::Coroutine(id.into(), substitution.to_nextsolver(ir))
                todo!("Needs GenericDefId::Coroutine")
            }
            chalk_ir::TyKind::CoroutineWitness(_coroutine_id, _substitution) => {
                //let id = ra_salsa::InternKey::from_intern_id(coroutine_id.0);
                //rustc_type_ir::TyKind::CoroutineWitness(id.into(), substitution.to_nextsolver(ir))
                todo!("Needs GenericDefId::Coroutine")
            }
            chalk_ir::TyKind::Foreign(_foreign_def_id) => {
                //let id = ra_salsa::InternKey::from_intern_id(foreign_def_id.0);
                //rustc_type_ir::TyKind::Foreign(id.into())
                todo!("Needs GenericDefId::Foreign")
            }
            chalk_ir::TyKind::Error => rustc_type_ir::TyKind::Error(ErrorGuaranteed),
            chalk_ir::TyKind::Placeholder(placeholder_index) => {
                rustc_type_ir::TyKind::Placeholder(PlaceholderTy::new(
                    placeholder_index.ui.to_nextsolver(ir),
                    rustc_type_ir::BoundVar::from_usize(placeholder_index.idx),
                ))
            }
            chalk_ir::TyKind::Dyn(dyn_ty) => {
                // exists<type> { for<...> ^1.0: ... }
                let bounds = BoundExistentialPredicates::new_from_iter(dyn_ty.bounds.skip_binders().iter(Interner).filter_map(|pred| {
                    // for<...> ^1.0: ...
                    let (val, binders) = pred.clone().into_value_and_skipped_binders();
                    let bound_vars = binders.to_nextsolver(ir);
                    let clause = match val {
                        chalk_ir::WhereClause::Implemented(trait_ref) => {
                            let trait_id = from_chalk_trait_id(trait_ref.trait_id);
                            if ir.db.trait_data(trait_id).is_auto {
                                ExistentialPredicate::AutoTrait(GenericDefId::TraitId(trait_id))
                            } else {
                                let def_id = GenericDefId::TraitId(trait_id);
                                let args = GenericArgs::new_from_iter(trait_ref.substitution.iter(Interner).skip(1).map(|a| a.clone().shifted_out(Interner).unwrap()).map(|a| a.to_nextsolver(ir)));
                                let trait_ref = ExistentialTraitRef::new_from_args(ir, def_id, args);
                                ExistentialPredicate::Trait(trait_ref)
                            }
                        }
                        chalk_ir::WhereClause::AliasEq(alias_eq) => {
                            let (def_id, args) = match &alias_eq.alias {
                                chalk_ir::AliasTy::Projection(projection) => {
                                    let id = from_assoc_type_id(projection.associated_ty_id);
                                    let args = GenericArgs::new_from_iter(projection.substitution.iter(Interner).skip(1).map(|a| a.clone().shifted_out(Interner).unwrap()).map(|a| a.to_nextsolver(ir)));
                                    (GenericDefId::TypeAliasId(id), args)
                                }
                                chalk_ir::AliasTy::Opaque(_) => todo!(),
                            };
                            let term = alias_eq.ty.clone().shifted_out(Interner).unwrap().to_nextsolver(ir).into();
                            let projection = ExistentialProjection::new_from_args(ir, def_id, args, term);
                            ExistentialPredicate::Projection((projection))
                        }
                        chalk_ir::WhereClause::LifetimeOutlives(lifetime_outlives) => return None,
                        chalk_ir::WhereClause::TypeOutlives(type_outlives) => return None,
                    };

                    Some(Binder::bind_with_vars(clause, bound_vars))
                }));
                let region = dyn_ty.lifetime.to_nextsolver(ir);
                let kind = rustc_type_ir::DynKind::Dyn;
                rustc_type_ir::TyKind::Dynamic(bounds, region, kind)
            }
            chalk_ir::TyKind::Alias(alias_ty) => {
                match alias_ty {
                    chalk_ir::AliasTy::Projection(projection_ty) => {
                        let def_id: TypeAliasId =
                            ra_salsa::InternKey::from_intern_id(projection_ty.associated_ty_id.0);
                        let alias_ty = rustc_type_ir::AliasTy::new_from_args(
                            ir,
                            def_id.into(),
                            projection_ty.substitution.to_nextsolver(ir),
                        );
                        rustc_type_ir::TyKind::Alias(
                            rustc_type_ir::AliasTyKind::Projection,
                            alias_ty,
                        )
                    }
                    chalk_ir::AliasTy::Opaque(_opaque_ty) => {
                        //let def_id: TypeAliasId = ra_salsa::InternKey::from_intern_id(opaque_ty.opaque_ty_id);
                        //let alias_ty = rustc_type_ir::AliasTy::new(DbInterner, def_id.into(), opaque_ty.substitution.to_nextsolver(ir));
                        //rustc_type_ir::TyKind::Alias(rustc_type_ir::AliasTyKind::Opaque, alias_ty)
                        todo!("Needs GenericDefId::ImplTraitId")
                    }
                }
            }
            chalk_ir::TyKind::Function(fn_pointer) => {
                let sig_tys = fn_pointer.clone().into_binders(Interner).to_nextsolver(ir);
                let header = rustc_type_ir::FnHeader {
                    abi: fn_pointer.sig.abi,
                    c_variadic: fn_pointer.sig.variadic,
                    safety: match fn_pointer.sig.safety {
                        chalk_ir::Safety::Safe => super::abi::Safety::Safe,
                        chalk_ir::Safety::Unsafe => super::abi::Safety::Unsafe,
                    },
                };

                rustc_type_ir::TyKind::FnPtr(sig_tys, header)
            }
            chalk_ir::TyKind::BoundVar(bound_var) => rustc_type_ir::TyKind::Bound(
                bound_var.debruijn.to_nextsolver(ir),
                BoundTy {
                    var: rustc_type_ir::BoundVar::from_usize(bound_var.index),
                    kind: BoundTyKind::Anon,
                },
            ),
            chalk_ir::TyKind::InferenceVar(inference_var, ty_variable_kind) => {
                rustc_type_ir::TyKind::Infer(
                    (inference_var.clone(), ty_variable_kind.clone()).to_nextsolver(ir),
                )
            }
        })
    }
}

impl ChalkToNextSolver<Region> for chalk_ir::Lifetime<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Region {
        Region::new(match self.data(Interner) {
            chalk_ir::LifetimeData::BoundVar(bound_var) => rustc_type_ir::RegionKind::ReBound(
                bound_var.debruijn.to_nextsolver(ir),
                BoundRegion {
                    var: rustc_type_ir::BoundVar::from_u32(bound_var.index as u32),
                    kind: BoundRegionKind::Anon,
                },
            ),
            chalk_ir::LifetimeData::InferenceVar(inference_var) => {
                rustc_type_ir::RegionKind::ReVar(rustc_type_ir::RegionVid::from_u32(
                    inference_var.index(),
                ))
            }
            chalk_ir::LifetimeData::Placeholder(placeholder_index) => {
                rustc_type_ir::RegionKind::RePlaceholder(PlaceholderRegion::new(
                    rustc_type_ir::UniverseIndex::from_u32(placeholder_index.ui.counter as u32),
                    rustc_type_ir::BoundVar::from_u32(placeholder_index.idx as u32),
                ))
            }
            chalk_ir::LifetimeData::Static => rustc_type_ir::RegionKind::ReStatic,
            chalk_ir::LifetimeData::Erased => rustc_type_ir::RegionKind::ReErased,
            chalk_ir::LifetimeData::Phantom(_, _) => {
                unreachable!()
            }
            chalk_ir::LifetimeData::Error => rustc_type_ir::RegionKind::ReError(ErrorGuaranteed),
        })
    }
}

impl ChalkToNextSolver<Const> for chalk_ir::Const<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Const {
        let data = self.data(Interner);
        Const::new(match &data.value {
            chalk_ir::ConstValue::BoundVar(bound_var) => rustc_type_ir::ConstKind::Bound(
                bound_var.debruijn.to_nextsolver(ir),
                rustc_type_ir::BoundVar::from_usize(bound_var.index),
            ),
            chalk_ir::ConstValue::InferenceVar(inference_var) => {
                rustc_type_ir::ConstKind::Infer(rustc_type_ir::InferConst::Var(
                    rustc_type_ir::ConstVid::from_u32(inference_var.index()),
                ))
            }
            chalk_ir::ConstValue::Placeholder(placeholder_index) => {
                rustc_type_ir::ConstKind::Placeholder(PlaceholderConst::new(
                    placeholder_index.ui.to_nextsolver(ir),
                    rustc_type_ir::BoundVar::from_usize(placeholder_index.idx),
                ))
            }
            chalk_ir::ConstValue::Concrete(concrete_const) => rustc_type_ir::ConstKind::Value(
                data.ty.to_nextsolver(ir),
                ValueConst::new(concrete_const.interned.clone()),
            ),
        })
    }
}

impl ChalkToNextSolver<rustc_type_ir::FnSigTys<DbInterner>> for chalk_ir::FnSubst<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::FnSigTys<DbInterner> {
        rustc_type_ir::FnSigTys {
            inputs_and_output: Tys::new_from_iter(self.0.iter(Interner).map(|g| g.assert_ty_ref(Interner).to_nextsolver(ir)))
        }
    }
}

impl<
        U: TypeVisitable<DbInterner>,
        T: Clone + ChalkToNextSolver<U> + HasInterner<Interner = Interner>,
    > ChalkToNextSolver<rustc_type_ir::Binder<DbInterner, U>> for chalk_ir::Binders<T>
{
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::Binder<DbInterner, U> {
        let (val, binders) = self.clone().into_value_and_skipped_binders();
        rustc_type_ir::Binder::bind_with_vars(val.to_nextsolver(ir), binders.to_nextsolver(ir))
    }
}

impl ChalkToNextSolver<BoundVarKinds> for chalk_ir::VariableKinds<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> BoundVarKinds {
        BoundVarKinds::new_from_iter(self.iter(Interner).map(|v| v.to_nextsolver(ir)))
    }
}

impl ChalkToNextSolver<BoundVarKind> for chalk_ir::VariableKind<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> BoundVarKind {
        match self {
            chalk_ir::VariableKind::Ty(_ty_variable_kind) => BoundVarKind::Ty(BoundTyKind::Anon),
            chalk_ir::VariableKind::Lifetime => BoundVarKind::Region(BoundRegionKind::Anon),
            chalk_ir::VariableKind::Const(_ty) => BoundVarKind::Const,
        }
    }
}

impl ChalkToNextSolver<GenericArg> for chalk_ir::GenericArg<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> GenericArg {
        match self.data(Interner) {
            chalk_ir::GenericArgData::Ty(ty) => ty.to_nextsolver(ir).into(),
            chalk_ir::GenericArgData::Lifetime(lifetime) => lifetime.to_nextsolver(ir).into(),
            chalk_ir::GenericArgData::Const(const_) => const_.to_nextsolver(ir).into(),
        }
    }
}
impl ChalkToNextSolver<GenericArgs> for chalk_ir::Substitution<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> GenericArgs {
        GenericArgs::new(self.iter(Interner).map(|arg| -> GenericArg {
            arg.to_nextsolver(ir)
        }))
    }
}

impl ChalkToNextSolver<Tys> for chalk_ir::Substitution<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Tys {
        Tys::new_from_iter(self.iter(Interner).map(|arg| -> Ty {
            match arg.data(Interner) {
                chalk_ir::GenericArgData::Ty(ty) => ty.to_nextsolver(ir),
                chalk_ir::GenericArgData::Lifetime(_) => unreachable!(),
                chalk_ir::GenericArgData::Const(_) => unreachable!(),
            }
        }))
    }
}

impl ChalkToNextSolver<rustc_type_ir::DebruijnIndex> for chalk_ir::DebruijnIndex {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::DebruijnIndex {
        rustc_type_ir::DebruijnIndex::from_u32(self.depth())
    }
}

impl ChalkToNextSolver<rustc_type_ir::UniverseIndex> for chalk_ir::UniverseIndex {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::UniverseIndex {
        rustc_type_ir::UniverseIndex::from_u32(self.counter as u32)
    }
}

impl ChalkToNextSolver<rustc_type_ir::InferTy>
    for (chalk_ir::InferenceVar, chalk_ir::TyVariableKind)
{
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::InferTy {
        match self.1 {
            chalk_ir::TyVariableKind::General => {
                rustc_type_ir::InferTy::TyVar(rustc_type_ir::TyVid::from_u32(self.0.index()))
            }
            chalk_ir::TyVariableKind::Integer => {
                rustc_type_ir::InferTy::IntVar(rustc_type_ir::IntVid::from_u32(self.0.index()))
            }
            chalk_ir::TyVariableKind::Float => {
                rustc_type_ir::InferTy::FloatVar(rustc_type_ir::FloatVid::from_u32(self.0.index()))
            }
        }
    }
}

impl ChalkToNextSolver<rustc_ast_ir::Mutability> for chalk_ir::Mutability {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_ast_ir::Mutability {
        match self {
            chalk_ir::Mutability::Mut => rustc_ast_ir::Mutability::Mut,
            chalk_ir::Mutability::Not => rustc_ast_ir::Mutability::Not,
        }
    }
}

impl ChalkToNextSolver<rustc_type_ir::Variance> for chalk_ir::Variance {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> rustc_type_ir::Variance {
        match self {
            chalk_ir::Variance::Covariant => rustc_type_ir::Variance::Covariant,
            chalk_ir::Variance::Invariant => rustc_type_ir::Variance::Invariant,
            chalk_ir::Variance::Contravariant => rustc_type_ir::Variance::Contravariant,
        }
    }
}

impl ChalkToNextSolver<VariancesOf> for chalk_ir::Variances<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> VariancesOf {
        VariancesOf::new_from_iter(self.as_slice(Interner).iter().map(|v| v.to_nextsolver(ir)))
    }
}

impl ChalkToNextSolver<Canonical<Goal<DbInterner, Predicate>>>
    for chalk_ir::Canonical<chalk_ir::InEnvironment<chalk_ir::Goal<Interner>>>
{
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Canonical<Goal<DbInterner, Predicate>> {
        let param_env = self.value.environment.to_nextsolver(ir);
        let variables = CanonicalVars::new_from_iter(self.binders.iter(Interner).map(
            |k| match &k.kind {
                chalk_ir::VariableKind::Ty(ty_variable_kind) => {
                    CanonicalVarInfo {
                        kind: rustc_type_ir::CanonicalVarKind::Ty(rustc_type_ir::CanonicalTyVarKind::General(UniverseIndex::ROOT))
                    }
                }
                chalk_ir::VariableKind::Lifetime => {
                    CanonicalVarInfo {
                        kind: rustc_type_ir::CanonicalVarKind::Region(UniverseIndex::ROOT)
                    }
                }
                chalk_ir::VariableKind::Const(ty) => {
                    CanonicalVarInfo {
                        kind: rustc_type_ir::CanonicalVarKind::Const(UniverseIndex::ROOT)
                    }
                }
            },
        ));
        Canonical {
            max_universe: UniverseIndex::ROOT,
            value: Goal::new(ir.interner(), param_env, self.value.goal.to_nextsolver(ir)),
            variables,
        }
    }
}

impl ChalkToNextSolver<Predicate> for chalk_ir::Goal<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Predicate {
        match self.data(Interner) {
            chalk_ir::GoalData::Quantified(quantifier_kind, binders) => {
                if !binders.binders.is_empty(Interner) {
                    todo!()
                }
                let (val, _) = binders.clone().into_value_and_skipped_binders();
                val.shifted_out(Interner).unwrap().to_nextsolver(ir)
            }
            chalk_ir::GoalData::Implies(program_clauses, goal) => todo!(),
            chalk_ir::GoalData::All(goals) => todo!(),
            chalk_ir::GoalData::Not(goal) => todo!(),
            chalk_ir::GoalData::EqGoal(eq_goal) => todo!(),
            chalk_ir::GoalData::SubtypeGoal(subtype_goal) => todo!(),
            chalk_ir::GoalData::DomainGoal(domain_goal) => match domain_goal {
                chalk_ir::DomainGoal::Holds(where_clause) => match where_clause {
                    chalk_ir::WhereClause::Implemented(trait_ref) => {
                        let predicate = TraitPredicate {
                            trait_ref: trait_ref.to_nextsolver(ir),
                            polarity: rustc_type_ir::PredicatePolarity::Positive,
                        };
                        let pred_kind = Binder::bind_with_vars(
                            shift_vars(DbInterner, PredicateKind::Clause(ClauseKind::Trait(predicate)), 1),
                            BoundVarKinds::new_from_iter([]),
                        );
                        Predicate::new(pred_kind)
                        
                    }
                    chalk_ir::WhereClause::AliasEq(alias_eq) => {
                        let projection = match &alias_eq.alias {
                            chalk_ir::AliasTy::Projection(p) => p,
                            _ => todo!(),
                        };
                        let def_id = GenericDefId::TypeAliasId(TypeAliasId::from_intern_id(projection.associated_ty_id.0));
                        let args = projection.substitution.to_nextsolver(ir);
                        let term: Ty = alias_eq.ty.to_nextsolver(ir);
                        let term: Term = term.into();
                        let predicate = ProjectionPredicate {
                            projection_term: AliasTerm::new_from_args(ir, def_id, args),
                            term,
                        };
                        let pred_kind = Binder::bind_with_vars(
                            shift_vars(DbInterner, PredicateKind::Clause(ClauseKind::Projection(predicate)), 1),
                            BoundVarKinds::new_from_iter([]),
                        );
                        Predicate::new(pred_kind)
                    }
                    chalk_ir::WhereClause::LifetimeOutlives(lifetime_outlives) => todo!(),
                    chalk_ir::WhereClause::TypeOutlives(type_outlives) => todo!(),
                },
                chalk_ir::DomainGoal::WellFormed(well_formed) => todo!(),
                chalk_ir::DomainGoal::FromEnv(_) => todo!(),
                chalk_ir::DomainGoal::Normalize(normalize) => todo!(),
                chalk_ir::DomainGoal::IsLocal(ty) => todo!(),
                chalk_ir::DomainGoal::IsUpstream(ty) => todo!(),
                chalk_ir::DomainGoal::IsFullyVisible(ty) => todo!(),
                chalk_ir::DomainGoal::LocalImplAllowed(trait_ref) => todo!(),
                chalk_ir::DomainGoal::Compatible => todo!(),
                chalk_ir::DomainGoal::DownstreamType(ty) => todo!(),
                chalk_ir::DomainGoal::Reveal => todo!(),
                chalk_ir::DomainGoal::ObjectSafe(trait_id) => todo!(),
            },
            chalk_ir::GoalData::CannotProve => todo!(),
        }
    }
}

impl ChalkToNextSolver<ParamEnv> for chalk_ir::Environment<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> ParamEnv {
        let clauses = Clauses::new_from_iter(self.clauses().iter(Interner).map(|c| {
            c.to_nextsolver(ir)
        }));
        dbg!(&clauses);
        let clauses = Clauses::new_from_iter(elaborate::elaborate(ir, clauses.iter()));
        dbg!(&clauses);
        ParamEnv {
            reveal: rustc_type_ir::solve::Reveal::UserFacing,
            clauses,
        }
        //self.canonical.value.environment
    }
}

impl ChalkToNextSolver<Clause> for chalk_ir::ProgramClause<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> Clause {
        Clause(Predicate::new(self.data(Interner).0.to_nextsolver(ir)))
    }
}

impl ChalkToNextSolver<PredicateKind> for chalk_ir::ProgramClauseImplication<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> PredicateKind {
        assert!(self.conditions.is_empty(Interner));
        assert!(self.constraints.is_empty(Interner));
        match &self.consequence {
            chalk_ir::DomainGoal::Holds(where_clause) => match where_clause {
                chalk_ir::WhereClause::Implemented(trait_ref) => {
                    let predicate = TraitPredicate {
                        trait_ref: trait_ref.to_nextsolver(ir),
                        polarity: rustc_type_ir::PredicatePolarity::Positive,
                    };
                    PredicateKind::Clause(ClauseKind::Trait(predicate))
                }
                chalk_ir::WhereClause::AliasEq(alias_eq) => {
                    let projection = match &alias_eq.alias {
                        chalk_ir::AliasTy::Projection(p) => p,
                        _ => todo!(),
                    };
                    let def_id = GenericDefId::TypeAliasId(TypeAliasId::from_intern_id(projection.associated_ty_id.0));
                    let args = projection.substitution.to_nextsolver(ir);
                    let term: Ty = alias_eq.ty.to_nextsolver(ir);
                    let term: Term = term.into();
                    let predicate = ProjectionPredicate {
                        projection_term: AliasTerm::new_from_args(ir, def_id, args),
                        term,
                    };
                    PredicateKind::Clause(ClauseKind::Projection(predicate))
                }
                chalk_ir::WhereClause::LifetimeOutlives(lifetime_outlives) => todo!(),
                chalk_ir::WhereClause::TypeOutlives(type_outlives) => todo!(),
            },
            chalk_ir::DomainGoal::WellFormed(well_formed) => todo!(),
            chalk_ir::DomainGoal::FromEnv(from_env) => match from_env {
                chalk_ir::FromEnv::Trait(trait_ref) => {
                    let predicate = TraitPredicate {
                        trait_ref: trait_ref.to_nextsolver(ir),
                        polarity: rustc_type_ir::PredicatePolarity::Positive,
                    };
                    PredicateKind::Clause(ClauseKind::Trait(predicate))
                }
                chalk_ir::FromEnv::Ty(ty) => {
                    PredicateKind::Clause(ClauseKind::WellFormed(GenericArg::Ty(ty.to_nextsolver(ir))))
                }
            },
            chalk_ir::DomainGoal::Normalize(normalize) => todo!(),
            chalk_ir::DomainGoal::IsLocal(ty) => todo!(),
            chalk_ir::DomainGoal::IsUpstream(ty) => todo!(),
            chalk_ir::DomainGoal::IsFullyVisible(ty) => todo!(),
            chalk_ir::DomainGoal::LocalImplAllowed(trait_ref) => todo!(),
            chalk_ir::DomainGoal::Compatible => todo!(),
            chalk_ir::DomainGoal::DownstreamType(ty) => todo!(),
            chalk_ir::DomainGoal::Reveal => todo!(),
            chalk_ir::DomainGoal::ObjectSafe(trait_id) => todo!(),
        }
    }
}

impl ChalkToNextSolver<TraitRef> for chalk_ir::TraitRef<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> TraitRef {
        let args = self.substitution.to_nextsolver(ir);
        TraitRef::new_from_args(
            ir,
            GenericDefId::TraitId(ra_salsa::InternKey::from_intern_id(self.trait_id.0)),
            args,
        )
    }
}

impl ChalkToNextSolver<PredicateKind> for chalk_ir::WhereClause<Interner> {
    fn to_nextsolver(&self, ir: DbIr<'_>) -> PredicateKind {
        match self {
            chalk_ir::WhereClause::Implemented(trait_ref) => PredicateKind::Clause(rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                trait_ref: trait_ref.to_nextsolver(ir),
                polarity: rustc_type_ir::PredicatePolarity::Positive,
            })),
            chalk_ir::WhereClause::AliasEq(alias_eq) => {
                let alias_ty = chalk_ir::Ty::new(Interner, chalk_ir::TyKind::Alias(alias_eq.alias.clone()));
                let alias_ty: Ty = alias_ty.to_nextsolver(ir);
                let (def_id, args) = match &alias_eq.alias {
                    chalk_ir::AliasTy::Projection(p) => {
                        let args: GenericArgs = p.substitution.to_nextsolver(ir);
                        (GenericDefId::TypeAliasId(TypeAliasId::from_intern_id(p.associated_ty_id.0)), args)
                    }
                    _ => todo!(),
                };
                let to_ty: Ty = alias_eq.ty.to_nextsolver(ir);
                PredicateKind::Clause(rustc_type_ir::ClauseKind::Projection(ProjectionPredicate {
                   projection_term: AliasTerm::new(ir, def_id, args),
                   term: to_ty.into(),
                }))
            }
            chalk_ir::WhereClause::LifetimeOutlives(lifetime_outlives) => todo!(),
            chalk_ir::WhereClause::TypeOutlives(type_outlives) => todo!(),
        }
    }
}
