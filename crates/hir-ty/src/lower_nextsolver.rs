//! Methods for lowering the HIR to types. There are two main cases here:
//!
//!  - Lowering a type reference like `&usize` or `Option<foo::bar::Baz>` to a
//!    type: The entry point for this is `TyLoweringContext::lower_ty`.
//!  - Building the type for an item: This happens through the `ty` query.
//!
//! This usually involves resolving names, collecting generic arguments etc.
use std::{
    cell::OnceCell,
    iter, mem,
    ops::{self, Not as _},
};

use base_db::CrateId;

use either::Either;
use hir_def::{
    expander::Expander, generics::{
        GenericParamDataRef, TypeParamProvenance, WherePredicate,
        WherePredicateTypeTarget,
    }, lang_item::LangItem, nameres::MacroSubNs, path::{GenericArg, Path, PathKind, PathSegment, PathSegments}, resolver::{HasResolver, LifetimeNs, Resolver, TypeNs}, type_ref::{
        ConstRef, LifetimeRef, TraitBoundModifier, TraitRef as HirTraitRef, TypeBound, TypeRef,
        TypeRefId, TypesMap, TypesSourceMap,
    }, AdtId, AssocItemId, CallableDefId, DefWithBodyId, EnumVariantId, FunctionId, GenericDefId, GenericParamId, ImplId, ItemContainerId, Lookup, OpaqueTyLoc, StructId, TraitId, TypeAliasId, TypeOrConstParamId, TypeOwnerId
};
use hir_expand::{name::Name, ExpandResult};
use intern::sym;
use la_arena::Arena;
use rustc_ast_ir::Mutability;
use rustc_hash::FxHashSet;
use rustc_pattern_analysis::Captures;
use rustc_type_ir::{fold::{shift_vars, TypeFoldable}, inherent::{Const as _, GenericArg as _, IntoKind as _, PlaceholderLike as _, Region as _, SliceLike, Ty as _}, visit::TypeVisitableExt, AliasTerm, AliasTyKind, BoundVar, ConstKind, DebruijnIndex, ExistentialPredicate, ExistentialProjection, ExistentialTraitRef, FnSig, OutlivesPredicate, ProjectionPredicate, TyKind::{self}, UniverseIndex};
use smallvec::SmallVec;
use stdx::never;
use syntax::ast;
use triomphe::Arc;

use crate::{
    all_super_traits, db::HirDatabase, generics::{generics, trait_self_param_idx, Generics}, next_solver::{abi::Safety, elaborate::{all_super_trait_refs, associated_type_by_name_including_super_traits}, fold::{BoundVarReplacer, FnMutDelegate}, mapping::{convert_binder_to_early_binder, to_placeholder_idx, ChalkToNextSolver}, util::apply_args_to_binder, AdtDef, AliasTy, Binder, BoundExistentialPredicates, BoundRegion, BoundRegionKind, BoundTy, BoundTyKind, BoundVarKind, BoundVarKinds, Clause, Const, DbInterner, EarlyBinder, EarlyParamRegion, ErrorGuaranteed, GenericArgs, ParamConst, Placeholder, PolyFnSig, Predicate, Region, TraitPredicate, TraitRef, Ty, Tys, ValueConst}, ConstScalar, FnAbi, ImplTrait, ParamKind, TyDefId, ValueTyDefId
};

#[derive(Debug, Default)]
struct ImplTraitLoweringState {
    /// When turning `impl Trait` into opaque types, we have to collect the
    /// bounds at the same time to get the IDs correct (without becoming too
    /// complicated).
    mode: ImplTraitLoweringMode,
    // This is structured as a struct with fields and not as an enum because it helps with the borrow checker.
    opaque_type_data: Arena<ImplTrait>,
    param_and_variable_counter: u16,
}
impl ImplTraitLoweringState {
    fn new(mode: ImplTraitLoweringMode) -> ImplTraitLoweringState {
        Self { mode, opaque_type_data: Arena::new(), param_and_variable_counter: 0 }
    }
    fn param(counter: u16) -> Self {
        Self {
            mode: ImplTraitLoweringMode::Param,
            opaque_type_data: Arena::new(),
            param_and_variable_counter: counter,
        }
    }
    fn variable(counter: u16) -> Self {
        Self {
            mode: ImplTraitLoweringMode::Variable,
            opaque_type_data: Arena::new(),
            param_and_variable_counter: counter,
        }
    }
}

#[derive(Debug)]
pub struct TyLoweringContext<'a> {
    pub db: &'a dyn HirDatabase,
    resolver: &'a Resolver,
    generics: OnceCell<Option<Generics>>,
    types_map: &'a TypesMap,
    /// If this is set, that means we're in a context of a freshly expanded macro, and that means
    /// we should not use `TypeRefId` in diagnostics because the caller won't have the `TypesMap`,
    /// instead we need to put `TypeSource` from the source map.
    types_source_map: Option<&'a TypesSourceMap>,
    in_binders: DebruijnIndex,
    // FIXME: Should not be an `Option` but `Resolver` currently does not return owners in all cases
    // where expected
    owner: Option<TypeOwnerId>,
    /// Note: Conceptually, it's thinkable that we could be in a location where
    /// some type params should be represented as placeholders, and others
    /// should be converted to variables. I think in practice, this isn't
    /// possible currently, so this should be fine for now.
    pub type_param_mode: ParamLoweringMode,
    impl_trait_mode: ImplTraitLoweringState,
    expander: Option<Expander>,
    /// Tracks types with explicit `?Sized` bounds.
    pub(crate) unsized_types: FxHashSet<Ty>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ParamLoweringMode {
    Placeholder,
    Variable,
    Param,
}

impl<'a> TyLoweringContext<'a> {
    pub fn new(
        db: &'a dyn HirDatabase,
        resolver: &'a Resolver,
        types_map: &'a TypesMap,
        owner: TypeOwnerId,
    ) -> Self {
        Self::new_maybe_unowned(db, resolver, types_map, None, Some(owner))
    }

    pub fn new_maybe_unowned(
        db: &'a dyn HirDatabase,
        resolver: &'a Resolver,
        types_map: &'a TypesMap,
        types_source_map: Option<&'a TypesSourceMap>,
        owner: Option<TypeOwnerId>,
    ) -> Self {
        let impl_trait_mode = ImplTraitLoweringState::new(ImplTraitLoweringMode::Disallowed);
        let type_param_mode = ParamLoweringMode::Placeholder;
        let in_binders = DebruijnIndex::ZERO;
        Self {
            db,
            resolver,
            generics: OnceCell::new(),
            types_map,
            types_source_map,
            owner,
            in_binders,
            impl_trait_mode,
            type_param_mode,
            expander: None,
            unsized_types: FxHashSet::default(),
        }
    }

    pub fn with_debruijn<T>(
        &mut self,
        debruijn: DebruijnIndex,
        f: impl FnOnce(&mut TyLoweringContext<'_>) -> T,
    ) -> T {
        let old_debruijn = mem::replace(&mut self.in_binders, debruijn);
        let result = f(self);
        self.in_binders = old_debruijn;
        result
    }

    pub fn with_shifted_in<T>(
        &mut self,
        debruijn: DebruijnIndex,
        f: impl FnOnce(&mut TyLoweringContext<'_>) -> T,
    ) -> T {
        self.with_debruijn(self.in_binders.shifted_in(debruijn.as_u32()), f)
    }

    pub fn with_impl_trait_mode(self, impl_trait_mode: ImplTraitLoweringMode) -> Self {
        Self { impl_trait_mode: ImplTraitLoweringState::new(impl_trait_mode), ..self }
    }

    pub fn with_type_param_mode(self, type_param_mode: ParamLoweringMode) -> Self {
        Self { type_param_mode, ..self }
    }

    pub fn impl_trait_mode(&mut self, impl_trait_mode: ImplTraitLoweringMode) -> &mut Self {
        self.impl_trait_mode = ImplTraitLoweringState::new(impl_trait_mode);
        self
    }

    pub fn type_param_mode(&mut self, type_param_mode: ParamLoweringMode) -> &mut Self {
        self.type_param_mode = type_param_mode;
        self
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum ImplTraitLoweringMode {
    /// `impl Trait` gets lowered into an opaque type that doesn't unify with
    /// anything except itself. This is used in places where values flow 'out',
    /// i.e. for arguments of the function we're currently checking, and return
    /// types of functions we're calling.
    Opaque,
    /// `impl Trait` gets lowered into a type variable. Used for argument
    /// position impl Trait when inside the respective function, since it allows
    /// us to support that without Chalk.
    Param,
    /// `impl Trait` gets lowered into a variable that can unify with some
    /// type. This is used in places where values flow 'in', i.e. for arguments
    /// of functions we're calling, and the return type of the function we're
    /// currently checking.
    Variable,
    /// `impl Trait` is disallowed and will be an error.
    #[default]
    Disallowed,
}

impl<'a> TyLoweringContext<'a> {
    pub fn lower_ty(&mut self, type_ref: TypeRefId) -> Ty {
        self.lower_ty_ext(type_ref).0
    }

    pub fn lower_const(&mut self, const_ref: &ConstRef, const_type: Ty) -> Const {
        let Some(owner) = self.owner else { return unknown_const(const_type) };
        let debruijn = self.in_binders;
        const_or_path_to_const(
            self.db,
            self.resolver,
            owner,
            const_type,
            const_ref,
            self.type_param_mode,
            || self.generics(),
            debruijn,
        )
    }

    fn generics(&self) -> Option<&Generics> {
        self.generics
            .get_or_init(|| self.resolver.generic_def().map(|def| generics(self.db.upcast(), def)))
            .as_ref()
    }

    pub fn lower_ty_ext(&mut self, type_ref_id: TypeRefId) -> (Ty, Option<TypeNs>) {
        let mut res = None;
        let type_ref = &self.types_map[type_ref_id];
        let ty = match type_ref {
            TypeRef::Never => Ty::new(TyKind::Never),
            TypeRef::Tuple(inner) => {
                let inner_tys = inner.iter().map(|&tr| self.lower_ty(tr));
                Ty::new_tup_from_iter(DbInterner, inner_tys)
            }
            TypeRef::Path(path) => {
                let (ty, res_) = self.lower_path(path);
                res = res_;
                ty
            }
            &TypeRef::RawPtr(inner, mutability) => {
                let inner_ty = self.lower_ty(inner);
                Ty::new(TyKind::RawPtr(inner_ty, lower_mutability(mutability)))
            }
            TypeRef::Array(array) => {
                let inner_ty = self.lower_ty(array.ty);
                let const_len = self.lower_const(&array.len, Ty::new_usize(DbInterner));
                Ty::new_array_with_const_len(DbInterner, inner_ty, const_len)
            }
            &TypeRef::Slice(inner) => {
                let inner_ty = self.lower_ty(inner);
                Ty::new_slice(DbInterner, inner_ty)
            }
            TypeRef::Reference(ref_) => {
                let inner_ty = self.lower_ty(ref_.ty);
                // FIXME: It should infer the eldided lifetimes instead of stubbing with error
                let lifetime = ref_
                    .lifetime
                    .as_ref()
                    .map_or_else(|| Region::error(), |lr| self.lower_lifetime(lr));
                Ty::new_ref(DbInterner, lifetime, inner_ty, lower_mutability(ref_.mutability))
            }
            TypeRef::Placeholder => Ty::new_error(DbInterner, ErrorGuaranteed),
            TypeRef::Fn(fn_) => {
                let substs = self.with_shifted_in(DebruijnIndex::from_u32(1), |ctx: &mut TyLoweringContext<'_>| {
                    Tys::new_from_iter(fn_.params().iter().map(|&(_, tr)| ctx.lower_ty(tr)))
                });
                Ty::new_fn_ptr(DbInterner, Binder::dummy(FnSig {
                    abi: fn_.abi().as_ref().map_or(FnAbi::Rust, FnAbi::from_symbol),
                    safety: if fn_.is_unsafe() { Safety::Unsafe } else { Safety::Safe },
                    c_variadic: fn_.is_varargs(),
                    inputs_and_output: substs,
                }))
            }
            TypeRef::DynTrait(bounds) => self.lower_dyn_trait(bounds),
            TypeRef::ImplTrait(bounds) => {
                match self.impl_trait_mode.mode {
                    ImplTraitLoweringMode::Opaque => {
                        let origin = match self.resolver.generic_def() {
                            Some(GenericDefId::FunctionId(it)) => Either::Left(it),
                            Some(GenericDefId::TypeAliasId(it)) => Either::Right(it),
                            _ => panic!(
                                "opaque impl trait lowering must be in function or type alias"
                            ),
                        };

                        // this dance is to make sure the data is in the right
                        // place even if we encounter more opaque types while
                        // lowering the bounds
                        let idx = self.impl_trait_mode.opaque_type_data.alloc(ImplTrait {
                            bounds: crate::make_single_type_binders(Vec::default()),
                        });
                        // We don't want to lower the bounds inside the binders
                        // we're currently in, because they don't end up inside
                        // those binders. E.g. when we have `impl Trait<impl
                        // OtherTrait<T>>`, the `impl OtherTrait<T>` can't refer
                        // to the self parameter from `impl Trait`, and the
                        // bounds aren't actually stored nested within each
                        // other, but separately. So if the `T` refers to a type
                        // parameter of the outer function, it's just one binder
                        // away instead of two.
                        let actual_opaque_type_data = self
                            .with_debruijn(DebruijnIndex::ZERO, |ctx| {
                                ctx.lower_impl_trait(bounds, self.resolver.krate())
                            });
                        // FIXME: need to copy `ImplTrait` and `ImplTraits` for next solver
                        //self.impl_trait_mode.opaque_type_data[idx] = actual_opaque_type_data;

                        let opaque_ty_loc = origin.either(
                            |f| OpaqueTyLoc::ReturnTypeImplTrait(f, idx.into_raw()),
                            |a| OpaqueTyLoc::TypeAliasImplTrait(a, idx.into_raw()),
                        );
                        let opaque_ty_id = self.db.intern_opaque_ty(opaque_ty_loc);
                        /*
                        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                        let args = GenericArgs::for_item(fake_ir, opaque_ty_id.into(), |param, _| match param.kind {
                            crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_u32(param.index()), kind: BoundTyKind::Anon }).into(),
                            crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion { var: BoundVar::from_u32(param.index()), kind: BoundRegionKind::Anon }).into(),
                            crate::next_solver::generics::GenericParamDefKind::Const => Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_u32(param.index())).into(),
                        });
                        Ty::new_alias(DbInterner, AliasTyKind::Opaque, AliasTy::new_from_args(fake_ir, opaque_ty_id.into(), args))
                        */
                        todo!()
                    }
                    ImplTraitLoweringMode::Param => {
                        let idx = self.impl_trait_mode.param_and_variable_counter;
                        // Count the number of `impl Trait` things that appear within our bounds.
                        // Since those have been emitted as implicit type args already.
                        self.impl_trait_mode.param_and_variable_counter =
                            idx + self.count_impl_traits(type_ref_id) as u16;
                        let db = self.db;
                        self
                            .generics()
                            .expect("param impl trait lowering must be in a generic def")
                            .iter()
                            .filter_map(|(id, data)| match (id, data) {
                                (
                                    GenericParamId::TypeParamId(id),
                                    GenericParamDataRef::TypeParamData(data),
                                ) if data.provenance == TypeParamProvenance::ArgumentImplTrait => {
                                    Some(id)
                                }
                                _ => None,
                            })
                            .nth(idx as usize)
                            .map_or(Ty::new_error(DbInterner, ErrorGuaranteed), |id| {
                                let interned_id = db.intern_type_or_const_param_id(id.into());
                                Ty::new_placeholder(Placeholder::new(UniverseIndex::ROOT, BoundVar::from_usize(base_db::ra_salsa::InternKey::as_intern_id(&interned_id).as_usize())))
                            })
                    }
                    ImplTraitLoweringMode::Variable => {
                        let idx = self.impl_trait_mode.param_and_variable_counter;
                        // Count the number of `impl Trait` things that appear within our bounds.
                        // Since t hose have been emitted as implicit type args already.
                        self.impl_trait_mode.param_and_variable_counter =
                            idx + self.count_impl_traits(type_ref_id) as u16;
                        let debruijn = self.in_binders;
                        self
                            .generics()
                            .expect("variable impl trait lowering must be in a generic def")
                            .iter()
                            .enumerate()
                            .filter_map(|(i, (id, data))| match (id, data) {
                                (
                                    GenericParamId::TypeParamId(_),
                                    GenericParamDataRef::TypeParamData(data),
                                ) if data.provenance == TypeParamProvenance::ArgumentImplTrait => {
                                    Some(i)
                                }
                                _ => None,
                            })
                            .nth(idx as usize)
                            .map_or(Ty::new_error(DbInterner, ErrorGuaranteed), |id| {
                                Ty::new_bound(DbInterner, debruijn, BoundTy { var: BoundVar::from_usize(id), kind: BoundTyKind::Anon })
                            })
                    }
                    ImplTraitLoweringMode::Disallowed => {
                        // FIXME: report error
                        Ty::new_error(DbInterner, ErrorGuaranteed)
                    }
                }
            }
            TypeRef::Macro(macro_call) => {
                let (expander, recursion_start) = {
                    match &mut self.expander {
                        // There already is an expander here, this means we are already recursing
                        Some(expander) => (expander, false),
                        // No expander was created yet, so we are at the start of the expansion recursion
                        // and therefore have to create an expander.
                        None => {
                            let expander = self.expander.insert(Expander::new(
                                self.db.upcast(),
                                macro_call.file_id,
                                self.resolver.module(),
                            ));
                            (expander, true)
                        }
                    }
                };
                let ty = {
                    let macro_call = macro_call.to_node(self.db.upcast());
                    let resolver = |path: &_| {
                        self.resolver
                            .resolve_path_as_macro(self.db.upcast(), path, Some(MacroSubNs::Bang))
                            .map(|(it, _)| it)
                    };
                    match expander.enter_expand::<ast::Type>(self.db.upcast(), macro_call, resolver)
                    {
                        Ok(ExpandResult { value: Some((mark, expanded)), .. }) => {
                            let (mut types_map, mut types_source_map) =
                                (TypesMap::default(), TypesSourceMap::default());

                            let mut ctx = expander.ctx(
                                self.db.upcast(),
                                &mut types_map,
                                &mut types_source_map,
                            );
                            // FIXME: Report syntax errors in expansion here
                            let type_ref = TypeRef::from_ast(&mut ctx, expanded.tree());

                            // Can't mutate `self`, must create a new instance, because of the lifetimes.
                            let mut inner_ctx = TyLoweringContext {
                                db: self.db,
                                resolver: self.resolver,
                                generics: self.generics.clone(),
                                types_map: &types_map,
                                types_source_map: Some(&types_source_map),
                                in_binders: self.in_binders,
                                owner: self.owner,
                                type_param_mode: self.type_param_mode,
                                impl_trait_mode: mem::take(&mut self.impl_trait_mode),
                                expander: self.expander.take(),
                                unsized_types: mem::take(&mut self.unsized_types),
                            };

                            let ty = inner_ctx.lower_ty(type_ref);

                            self.impl_trait_mode = inner_ctx.impl_trait_mode;
                            self.expander = inner_ctx.expander;
                            self.unsized_types = inner_ctx.unsized_types;

                            self.expander.as_mut().unwrap().exit(mark);
                            Some(ty)
                        }
                        _ => None,
                    }
                };

                // drop the expander, resetting it to pre-recursion state
                if recursion_start {
                    self.expander = None;
                }
                ty.unwrap_or_else(|| Ty::new_error(DbInterner, ErrorGuaranteed))
            }
            TypeRef::Error => Ty::new_error(DbInterner, ErrorGuaranteed),
        };
        (ty, res)
    }

    /// This is only for `generic_predicates_for_param`, where we can't just
    /// lower the self types of the predicates since that could lead to cycles.
    /// So we just check here if the `type_ref` resolves to a generic param, and which.
    fn lower_ty_only_param(&self, type_ref: TypeRefId) -> Option<TypeOrConstParamId> {
        let type_ref = &self.types_map[type_ref];
        let path = match type_ref {
            TypeRef::Path(path) => path,
            _ => return None,
        };
        if path.type_anchor().is_some() {
            return None;
        }
        if path.segments().len() > 1 {
            return None;
        }
        let resolution = match self.resolver.resolve_path_in_type_ns(self.db.upcast(), path) {
            Some((it, None, _)) => it,
            _ => return None,
        };
        match resolution {
            TypeNs::GenericParam(param_id) => Some(param_id.into()),
            _ => None,
        }
    }

    pub(crate) fn lower_ty_relative_path(
        &mut self,
        ty: Ty,
        // We need the original resolution to lower `Self::AssocTy` correctly
        res: Option<TypeNs>,
        remaining_segments: PathSegments<'_>,
    ) -> (Ty, Option<TypeNs>) {
        match remaining_segments.len() {
            0 => (ty, res),
            1 => {
                // resolve unselected assoc types
                let segment = remaining_segments.first().unwrap();
                (self.select_associated_type(res, segment), None)
            }
            _ => {
                // FIXME report error (ambiguous associated type)
                (Ty::new_error(DbInterner, ErrorGuaranteed), None)
            }
        }
    }

    pub(crate) fn lower_partly_resolved_path(
        &mut self,
        resolution: TypeNs,
        resolved_segment: PathSegment<'_>,
        remaining_segments: PathSegments<'_>,
        infer_args: bool,
    ) -> (Ty, Option<TypeNs>) {
        let ty = match resolution {
            TypeNs::TraitId(trait_) => {
                let ty = match remaining_segments.len() {
                    1 => {
                        let trait_ref = self.lower_trait_ref_from_resolved_path(
                            trait_,
                            resolved_segment,
                            Ty::new_error(DbInterner, ErrorGuaranteed),
                        );
                        let segment = remaining_segments.first().unwrap();
                        let trait_id = match trait_ref.def_id {
                            GenericDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        let found = self
                            .db
                            .trait_data(trait_id)
                            .associated_type_by_name(segment.name);

                        match found {
                            Some(associated_ty) => {
                                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                                // that method to optionally take parent `Substitution` as we already know them at
                                // this point (`trait_ref.substitution`).
                                let substitution = self.substs_from_path_segment(
                                    segment,
                                    Some(associated_ty.into()),
                                    false,
                                    None,
                                );
                                let len_self =
                                    generics(self.db.upcast(), associated_ty.into()).len_self();
                                let args = GenericArgs::new_from_iter(substitution.iter().take(len_self).chain(trait_ref.args.iter()));
                                let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                                Ty::new_alias(DbInterner, AliasTyKind::Projection, AliasTy::new_from_args(fake_ir, associated_ty.into(), args))
                            }
                            None => {
                                // FIXME: report error (associated type not found)
                                Ty::new_error(DbInterner, ErrorGuaranteed)
                            }
                        }
                    }
                    0 => {
                        // Trait object type without dyn; this should be handled in upstream. See
                        // `lower_path()`.
                        stdx::never!("unexpected fully resolved trait path");
                        Ty::new_error(DbInterner, ErrorGuaranteed)
                    }
                    _ => {
                        // FIXME report error (ambiguous associated type)
                        Ty::new_error(DbInterner, ErrorGuaranteed)
                    }
                };
                return (ty, None);
            }
            TypeNs::TraitAliasId(_) => {
                // FIXME(trait_alias): Implement trait alias.
                return (Ty::new_error(DbInterner, ErrorGuaranteed), None);
            }
            TypeNs::GenericParam(param_id) => match self.type_param_mode {
                ParamLoweringMode::Placeholder => {
                    let interned_id = self.db.intern_type_or_const_param_id(param_id.into());
                    let idx = base_db::ra_salsa::InternKey::as_intern_id(&interned_id).as_usize();
                    Ty::new_placeholder(Placeholder::new(UniverseIndex::ROOT, BoundVar::from_usize(idx)))
                }
                ParamLoweringMode::Variable => {
                    let idx = match self
                        .generics()
                        .expect("generics in scope")
                        .type_or_const_param_idx(param_id.into())
                    {
                        None => {
                            never!("no matching generics");
                            return (Ty::new_error(DbInterner, ErrorGuaranteed), None);
                        }
                        Some(idx) => idx,
                    };

                    let bound = BoundTy {
                        var: BoundVar::from_usize(idx),
                        kind: crate::next_solver::BoundTyKind::Anon,
                    };
                    Ty::new_bound(DbInterner, DebruijnIndex::from_u32(self.in_binders.as_u32()), bound)
                }
                ParamLoweringMode::Param => {
                    let generics = self
                        .generics()
                        .expect("generics in scope");
                    match generics.type_or_const_param_idx(param_id.into()) {
                        None => {
                            never!("no matching generics");
                            Ty::new_error(DbInterner, ErrorGuaranteed)
                        }
                        Some(idx) => {
                            Ty::new_param(idx as u32, sym::MISSING_NAME.clone())
                        },
                    }
                }
            }
            TypeNs::SelfType(impl_id) => {
                let generics = self.generics().expect("impl should have generic param scope");

                match self.type_param_mode {
                    ParamLoweringMode::Placeholder => {
                        // `def` can be either impl itself or item within, and we need impl itself
                        // now.
                        let generics = generics.parent_or_self();
                        let subst = generics.placeholder_subst(self.db);

                        // FIXME: use db query
                        let self_ty = impl_self_ty_query(self.db, impl_id);
                        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                        let types = &mut |ty: BoundTy| { subst.at(crate::Interner, ty.var.index()).assert_ty_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let regions = &mut |region: BoundRegion| { subst.at(crate::Interner, region.var.index()).assert_lifetime_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let consts = &mut |const_: BoundVar| { subst.at(crate::Interner, const_.index()).assert_const_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let mut instantiate = BoundVarReplacer::new(DbInterner, FnMutDelegate {
                            types,
                            regions,
                            consts,
                        });
                        self_ty.fold_with(&mut instantiate).skip_binder()
                    }
                    ParamLoweringMode::Variable => {
                        let starting_from = match generics.def() {
                            GenericDefId::ImplId(_) => 0,
                            // `def` is an item within impl. We need to substitute `BoundVar`s but
                            // remember that they are for parent (i.e. impl) generic params so they
                            // come after our own params.
                            _ => generics.len_self(),
                        };

                        let generics = crate::generics::generics(self.db.upcast(), impl_id.into());
                        assert!(generics.parent_generics().is_none());
                        let params = generics
                            .iter_self()
                            .map(|(id, _data)| match id {
                                GenericParamId::TypeParamId(_) => ParamKind::Type,
                                GenericParamId::ConstParamId(id) => ParamKind::Const(self.db.const_param_ty(id)),
                                GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
                            });

                        let args = GenericArgs::new_from_iter((starting_from..).zip(params).map(|(idx, kind)| match kind {
                            ParamKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy {
                                var: BoundVar::from_usize(idx),
                                kind: BoundTyKind::Anon,
                            }).into(),
                            ParamKind::Const(_ty) => {
                                Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_usize(idx)).into()
                            }
                            ParamKind::Lifetime => {
                                Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion {
                                    var: BoundVar::from_usize(idx),
                                    kind: BoundRegionKind::Anon,
                                }).into()
                            }
                        }));

                        // FIXE: use db query
                        let self_ty = impl_self_ty_query(self.db, impl_id);
                        let types = &mut |ty: BoundTy| { args.as_slice()[ty.var.index()].expect_ty() };
                        let regions = &mut |region: BoundRegion| { args.as_slice()[region.var.index()].expect_region() };
                        let consts = &mut |const_: BoundVar| { args.as_slice()[const_.index()].expect_const() };
                        let mut instantiate = BoundVarReplacer::new(DbInterner, FnMutDelegate {
                            types,
                            regions,
                            consts,
                        });
                        self_ty.fold_with(&mut instantiate).skip_binder()
                    }
                    ParamLoweringMode::Param => {
                        let starting_from = match generics.def() {
                            GenericDefId::ImplId(_) => 0,
                            // `def` is an item within impl. We need to substitute `BoundVar`s but
                            // remember that they are for parent (i.e. impl) generic params so they
                            // come after our own params.
                            _ => generics.len_self(),
                        };

                        let generics = crate::generics::generics(self.db.upcast(), impl_id.into());
                        assert!(generics.parent_generics().is_none());
                        let params = generics
                            .iter_self()
                            .map(|(id, _data)| match id {
                                GenericParamId::TypeParamId(_) => ParamKind::Type,
                                GenericParamId::ConstParamId(id) => ParamKind::Const(self.db.const_param_ty(id)),
                                GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
                            });

                        let args = GenericArgs::new_from_iter((starting_from..).zip(params).map(|(idx, kind)| match kind {
                            ParamKind::Type => Ty::new_param(idx as u32, sym::MISSING_NAME.clone()).into(),
                            ParamKind::Lifetime => Region::new_early_param(EarlyParamRegion { index: idx as u32, name: sym::MISSING_NAME.clone() }).into(),
                            ParamKind::Const(_) => Const::new_param(ParamConst { index: idx as u32, name: sym::MISSING_NAME.clone() }).into(),
                        }));

                        // FIXE: use db query
                        let self_ty = impl_self_ty_query(self.db, impl_id);
                        let types = &mut |ty: BoundTy| { args.as_slice()[ty.var.index()].expect_ty() };
                        let regions = &mut |region: BoundRegion| { args.as_slice()[region.var.index()].expect_region() };
                        let consts = &mut |const_: BoundVar| { args.as_slice()[const_.index()].expect_const() };
                        let mut instantiate = BoundVarReplacer::new(DbInterner, FnMutDelegate {
                            types,
                            regions,
                            consts,
                        });
                        self_ty.fold_with(&mut instantiate).skip_binder()
                    }
                }
            }
            TypeNs::AdtSelfType(adt) => {
                let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                let args = match self.type_param_mode {
                    ParamLoweringMode::Placeholder => GenericArgs::for_item(fake_ir, adt.into(), |param, _| match param.kind {
                        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_placeholder(Placeholder { universe: UniverseIndex::ROOT, bound: BoundTy { var: BoundVar::from_u32(param.index()), kind: BoundTyKind::Anon } }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_placeholder(Placeholder { universe: UniverseIndex::ROOT, bound: BoundRegion { var: BoundVar::from_u32(param.index()), kind: BoundRegionKind::Anon } }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_placeholder(Placeholder { universe: UniverseIndex::ROOT, bound: BoundVar::from_u32(param.index()) }).into(),
                    }),
                    ParamLoweringMode::Variable => GenericArgs::for_item(fake_ir, adt.into(), |param, _| match param.kind {
                        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_u32(param.index()), kind: BoundTyKind::Anon }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion { var: BoundVar::from_u32(param.index()), kind: BoundRegionKind::Anon }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_u32(param.index())).into(),
                    }),
                    ParamLoweringMode::Param => GenericArgs::for_item(fake_ir, adt.into(), |param, _| match param.kind {
                        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_param(param.index(), param.name.clone()).into(),
                        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_early_param(EarlyParamRegion { index: param.index(), name: param.name.clone() }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_param(ParamConst { index: param.index(), name: param.name.clone() }).into(),
                    }),
                };
                Ty::new_adt(DbInterner, AdtDef::new(adt.into(), self.db), args)
            }

            TypeNs::AdtId(it) => self.lower_path_inner(resolved_segment, it.into(), infer_args),
            TypeNs::BuiltinType(it) => {
                self.lower_path_inner(resolved_segment, it.into(), infer_args)
            }
            TypeNs::TypeAliasId(it) => {
                self.lower_path_inner(resolved_segment, it.into(), infer_args)
            }
            // FIXME: report error
            TypeNs::EnumVariantId(_) => return (Ty::new_error(DbInterner, ErrorGuaranteed), None),
        };
        self.lower_ty_relative_path(ty, Some(resolution), remaining_segments)
    }

    pub(crate) fn lower_path(&mut self, path: &Path) -> (Ty, Option<TypeNs>) {
        // Resolve the path (in type namespace)
        if let Some(type_ref) = path.type_anchor() {
            let (ty, res) = self.lower_ty_ext(type_ref);
            return self.lower_ty_relative_path(ty, res, path.segments());
        }

        let (resolution, remaining_index, _) =
            match self.resolver.resolve_path_in_type_ns(self.db.upcast(), path) {
                Some(it) => it,
                None => return (Ty::new_error(DbInterner, ErrorGuaranteed), None),
            };

        if matches!(resolution, TypeNs::TraitId(_)) && remaining_index.is_none() {
            // trait object type without dyn
            let bound = TypeBound::Path(path.clone(), TraitBoundModifier::None);
            let ty = self.lower_dyn_trait(&[bound]);
            return (ty, None);
        }

        let (resolved_segment, remaining_segments) = match remaining_index {
            None => (
                path.segments().last().expect("resolved path has at least one element"),
                PathSegments::EMPTY,
            ),
            Some(i) => (path.segments().get(i - 1).unwrap(), path.segments().skip(i)),
        };
        self.lower_partly_resolved_path(resolution, resolved_segment, remaining_segments, false)
    }

    fn select_associated_type(&mut self, res: Option<TypeNs>, segment: PathSegment<'_>) -> Ty {
        let Some((generics, res)) = self.generics().zip(res) else {
            return Ty::new_error(DbInterner, ErrorGuaranteed);
        };
        let ty = named_associated_type_shorthand_candidates(
            self.db,
            generics.def(),
            res,
            Some(segment.name.clone()),
            move |name, t, associated_ty| {
                let generics = self.generics().unwrap();

                if name != segment.name {
                    return None;
                }

                let parent_subst = t.args.clone();
                let parent_subst = match self.type_param_mode {
                    ParamLoweringMode::Placeholder => {
                        // if we're lowering to placeholders, we have to put them in now.
                        let subst = generics.placeholder_subst(self.db);

                        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                        let types = &mut |ty: BoundTy| { subst.at(crate::Interner, ty.var.index()).assert_ty_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let regions = &mut |region: BoundRegion| { subst.at(crate::Interner, region.var.index()).assert_lifetime_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let consts = &mut |const_: BoundVar| { subst.at(crate::Interner, const_.index()).assert_const_ref(crate::Interner).to_nextsolver(fake_ir) };
                        let mut instantiate = BoundVarReplacer::new(DbInterner, FnMutDelegate {
                            types,
                            regions,
                            consts,
                        });
                        parent_subst.fold_with(&mut instantiate)
                    }
                    ParamLoweringMode::Variable => {
                        // We need to shift in the bound vars, since
                        // `named_associated_type_shorthand_candidates` does not do that.
                        shift_vars(DbInterner, parent_subst, self.in_binders.as_u32())
                    }
                    ParamLoweringMode::Param => {
                        let params = generics
                            .iter()
                            .map(|(id, _data)| match id {
                                GenericParamId::TypeParamId(_) => ParamKind::Type,
                                GenericParamId::ConstParamId(id) => ParamKind::Const(self.db.const_param_ty(id)),
                                GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
                            });

                        let args = GenericArgs::new_from_iter(params.enumerate().map(|(idx, kind)| match kind {
                            ParamKind::Type => Ty::new_param(idx as u32, sym::MISSING_NAME.clone()).into(),
                            ParamKind::Lifetime => Region::new_early_param(EarlyParamRegion { index: idx as u32, name: sym::MISSING_NAME.clone() }).into(),
                            ParamKind::Const(_) => Const::new_param(ParamConst { index: idx as u32, name: sym::MISSING_NAME.clone() }).into(),
                        }));

                        let types = &mut |ty: BoundTy| { args.as_slice()[ty.var.index()].expect_ty() };
                        let regions = &mut |region: BoundRegion| { args.as_slice()[region.var.index()].expect_region() };
                        let consts = &mut |const_: BoundVar| { args.as_slice()[const_.index()].expect_const() };
                        let mut instantiate = BoundVarReplacer::new(DbInterner, FnMutDelegate {
                            types,
                            regions,
                            consts,
                        });
                        parent_subst.fold_with(&mut instantiate)
                    }
                };

                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                // that method to optionally take parent `Substitution` as we already know them at
                // this point (`t.substitution`).
                let substs = self.substs_from_path_segment(
                    segment.clone(),
                    Some(associated_ty.into()),
                    false,
                    None,
                );

                let len_self =
                    crate::generics::generics(self.db.upcast(), associated_ty.into()).len_self();

                let substs = GenericArgs::new_from_iter(
                    substs.iter().take(len_self).chain(parent_subst.iter()),
                );

                let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                Some(Ty::new_alias(DbInterner, AliasTyKind::Projection, AliasTy::new(fake_ir, associated_ty.into(), substs)))
            },
        );

        ty.unwrap_or_else(|| Ty::new_error(DbInterner, ErrorGuaranteed))
    }

    fn lower_path_inner(
        &mut self,
        segment: PathSegment<'_>,
        typeable: TyDefId,
        infer_args: bool,
    ) -> Ty {
        let generic_def = match typeable {
            TyDefId::BuiltinType(_) => None,
            TyDefId::AdtId(it) => Some(it.into()),
            TyDefId::TypeAliasId(it) => Some(it.into()),
        };
        let substs = self.substs_from_path_segment(segment, generic_def, infer_args, None);
        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
        apply_args_to_binder(self.db.ty(typeable).to_nextsolver(fake_ir), substs, self.db)
    }

    /// Collect generic arguments from a path into a `Substs`. See also
    /// `create_substs_for_ast_path` and `def_to_ty` in rustc.
    pub(super) fn substs_from_path(
        &mut self,
        path: &Path,
        // Note that we don't call `db.value_type(resolved)` here,
        // `ValueTyDefId` is just a convenient way to pass generics and
        // special-case enum variants
        resolved: ValueTyDefId,
        infer_args: bool,
    ) -> GenericArgs {
        let last = path.segments().last();
        let (segment, generic_def) = match resolved {
            ValueTyDefId::FunctionId(it) => (last, Some(it.into())),
            ValueTyDefId::StructId(it) => (last, Some(it.into())),
            ValueTyDefId::UnionId(it) => (last, Some(it.into())),
            ValueTyDefId::ConstId(it) => (last, Some(it.into())),
            ValueTyDefId::StaticId(_) => (last, None),
            ValueTyDefId::EnumVariantId(var) => {
                // the generic args for an enum variant may be either specified
                // on the segment referring to the enum, or on the segment
                // referring to the variant. So `Option::<T>::None` and
                // `Option::None::<T>` are both allowed (though the former is
                // preferred). See also `def_ids_for_path_segments` in rustc.
                let len = path.segments().len();
                let penultimate = len.checked_sub(2).and_then(|idx| path.segments().get(idx));
                let segment = match penultimate {
                    Some(segment) if segment.args_and_bindings.is_some() => Some(segment),
                    _ => last,
                };
                (segment, Some(var.lookup(self.db.upcast()).parent.into()))
            }
        };
        if let Some(segment) = segment {
            self.substs_from_path_segment(segment, generic_def, infer_args, None)
        } else if let Some(generic_def) = generic_def {
            // lang item
            self.substs_from_args_and_bindings(None, Some(generic_def), infer_args, None)
        } else {
            GenericArgs::new_from_iter([])
        }
    }

    pub(super) fn substs_from_path_segment(
        &mut self,
        segment: PathSegment<'_>,
        def: Option<GenericDefId>,
        infer_args: bool,
        explicit_self_ty: Option<Ty>,
    ) -> GenericArgs {
        self.substs_from_args_and_bindings(
            segment.args_and_bindings,
            def,
            infer_args,
            explicit_self_ty,
        )
    }

    fn substs_from_args_and_bindings(
        &mut self,
        args_and_bindings: Option<&hir_def::path::GenericArgs>,
        def: Option<GenericDefId>,
        infer_args: bool,
        explicit_self_ty: Option<Ty>,
    ) -> GenericArgs {
        let Some(def) = def else { return GenericArgs::new_from_iter([]) };

        // Order is
        // - Optional Self parameter
        // - Lifetime parameters
        // - Type or Const parameters
        // - Parent parameters
        let def_generics = generics(self.db.upcast(), def);
        let (
            parent_params,
            self_param,
            type_params,
            const_params,
            impl_trait_params,
            lifetime_params,
        ) = def_generics.provenance_split();
        let item_len =
            self_param as usize + type_params + const_params + impl_trait_params + lifetime_params;
        let total_len = parent_params + item_len;

        let mut substs: Vec<crate::next_solver::GenericArg> = Vec::new();

        // we need to iterate the lifetime and type/const params separately as our order of them
        // differs from the supplied syntax

        let ty_error = || Ty::new_error(DbInterner, ErrorGuaranteed);
        let mut def_toc_iter = def_generics.iter_self_type_or_consts_id();
        let fill_self_param = || {
            if self_param {
                let self_ty = explicit_self_ty.map(|x| x.into()).unwrap_or_else(ty_error);

                if let Some(id) = def_toc_iter.next() {
                    assert!(matches!(id, GenericParamId::TypeParamId(_)));
                    substs.push(self_ty.into());
                }
            }
        };
        let mut had_explicit_args = false;

        if let Some(&hir_def::path::GenericArgs { ref args, has_self_type, .. }) = args_and_bindings {
            // Fill in the self param first
            if has_self_type && self_param {
                had_explicit_args = true;
                if let Some(id) = def_toc_iter.next() {
                    assert!(matches!(id, GenericParamId::TypeParamId(_)));
                    had_explicit_args = true;
                    if let GenericArg::Type(ty) = &args[0] {
                        substs.push(self.lower_ty(*ty).into());
                    }
                }
            } else {
                fill_self_param()
            };

            // Then fill in the supplied lifetime args, or error lifetimes if there are too few
            // (default lifetimes aren't a thing)
            for arg in args
                .iter()
                .filter_map(|arg| match arg {
                    GenericArg::Lifetime(arg) => Some(self.lower_lifetime(arg)),
                    _ => None,
                })
                .chain(iter::repeat_with(|| Region::error()))
                .take(lifetime_params)
            {
                substs.push(arg.into());
            }

            let skip = if has_self_type { 1 } else { 0 };
            // Fill in supplied type and const args
            // Note if non-lifetime args are provided, it should be all of them, but we can't rely on that
            for (arg, id) in args
                .iter()
                .filter(|arg| !matches!(arg, GenericArg::Lifetime(_)))
                .skip(skip)
                .take(type_params + const_params)
                .zip(def_toc_iter)
            {
                had_explicit_args = true;
                let arg = lower_generic_arg(
                    self.db,
                    id,
                    arg,
                    self,
                    self.types_map,
                    |this, type_ref| this.lower_ty(type_ref),
                    |this, const_ref, ty| this.lower_const(const_ref, ty),
                    |this, lifetime_ref| this.lower_lifetime(lifetime_ref),
                );
                substs.push(arg);
            }
        } else {
            fill_self_param();
        }

        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
        let param_to_err = |id| match id {
            GenericParamId::ConstParamId(x) => unknown_const(self.db.const_param_ty(x).to_nextsolver(fake_ir)).into(),
            GenericParamId::TypeParamId(_) => Ty::new_error(DbInterner, ErrorGuaranteed).into(),
            GenericParamId::LifetimeParamId(_) => Region::error().into(),
        };
        // handle defaults. In expression or pattern path segments without
        // explicitly specified type arguments, missing type arguments are inferred
        // (i.e. defaults aren't used).
        // Generic parameters for associated types are not supposed to have defaults, so we just
        // ignore them.
        let is_assoc_ty = || match def {
            GenericDefId::TypeAliasId(id) => {
                matches!(id.lookup(self.db.upcast()).container, ItemContainerId::TraitId(_))
            }
            _ => false,
        };
        let fill_defaults = (!infer_args || had_explicit_args) && !is_assoc_ty();
        if fill_defaults {
            let defaults = &*self.db.generic_defaults(def);
            let (item, _parent) = defaults.split_at(item_len);
            let parent_from = item_len - substs.len();

            let mut rem =
                def_generics.iter_id().skip(substs.len()).map(param_to_err).collect::<Vec<_>>();
            let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
            // Fill in defaults for type/const params
            for (idx, default_ty) in item[substs.len()..].iter().enumerate() {
                // each default can depend on the previous parameters
                let substs_so_far = GenericArgs::new_from_iter(substs.iter().cloned().chain(rem[idx..].iter().cloned()));
                substs.push(apply_args_to_binder(default_ty.to_nextsolver(fake_ir), substs_so_far, self.db));
            }
            // Fill in remaining parent params
            substs.extend(rem.drain(parent_from..));
        } else {
            // Fill in remaining def params and parent params
            substs.extend(def_generics.iter_id().skip(substs.len()).map(param_to_err));
        }

        assert_eq!(substs.len(), total_len, "expected {} substs, got {}", total_len, substs.len());
        GenericArgs::new_from_iter(substs)
    }

    pub(crate) fn lower_trait_ref_from_resolved_path(
        &mut self,
        resolved: TraitId,
        segment: PathSegment<'_>,
        explicit_self_ty: Ty,
    ) -> TraitRef {
        let substs = self.trait_ref_substs_from_path(segment, resolved, explicit_self_ty);
        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
        TraitRef::new_from_args(fake_ir, resolved.into(), substs)
    }

    fn lower_trait_ref_from_path(&mut self, path: &Path, explicit_self_ty: Ty) -> Option<TraitRef> {
        let resolved = match self.resolver.resolve_path_in_type_ns_fully(self.db.upcast(), path)? {
            // FIXME(trait_alias): We need to handle trait alias here.
            TypeNs::TraitId(tr) => tr,
            _ => return None,
        };
        let segment = path.segments().last().expect("path should have at least one segment");
        Some(self.lower_trait_ref_from_resolved_path(resolved, segment, explicit_self_ty))
    }

    fn lower_trait_ref(
        &mut self,
        trait_ref: &HirTraitRef,
        explicit_self_ty: Ty,
    ) -> Option<TraitRef> {
        self.lower_trait_ref_from_path(&trait_ref.path, explicit_self_ty)
    }

    fn trait_ref_substs_from_path(
        &mut self,
        segment: PathSegment<'_>,
        resolved: TraitId,
        explicit_self_ty: Ty,
    ) -> GenericArgs {
        self.substs_from_path_segment(segment, Some(resolved.into()), false, Some(explicit_self_ty))
    }

    pub(crate) fn lower_where_predicate<'b>(
        &'b mut self,
        where_predicate: &'b WherePredicate,
        &def: &GenericDefId,
        ignore_bindings: bool,
    ) -> impl Iterator<Item = Clause> + use<'a, 'b> {
        match where_predicate {
            WherePredicate::ForLifetime { target, bound, .. }
            | WherePredicate::TypeBound { target, bound } => {
                let self_ty = match target {
                    WherePredicateTypeTarget::TypeRef(type_ref) => self.lower_ty(*type_ref),
                    &WherePredicateTypeTarget::TypeOrConstParam(local_id) => {
                        let param_id = hir_def::TypeOrConstParamId { parent: def, local_id };
                        match self.type_param_mode {
                            ParamLoweringMode::Placeholder => {
                                Ty::new_placeholder(to_placeholder_idx(self.db, param_id, |var| BoundTy { var, kind: BoundTyKind::Anon }))
                            }
                            ParamLoweringMode::Variable => {
                                let idx = generics(self.db.upcast(), def)
                                    .type_or_const_param_idx(param_id)
                                    .expect("matching generics");
                                Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_usize(idx), kind: BoundTyKind::Anon })
                            }
                            ParamLoweringMode::Param => {
                                let idx = generics(self.db.upcast(), def)
                                    .type_or_const_param_idx(param_id)
                                    .expect("matching generics");
                                Ty::new_param(idx as u32, sym::MISSING_NAME.clone())
                            }
                        }
                    }
                };
                Either::Left(self.lower_type_bound(bound, self_ty, ignore_bindings))
            }
            WherePredicate::Lifetime { bound, target } => Either::Right(iter::once(
                Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::RegionOutlives(OutlivesPredicate(self.lower_lifetime(bound), self.lower_lifetime(target))))))
            ))),
        }
        .into_iter()
    }

    pub(crate) fn lower_type_bound<'b>(
        &'b mut self,
        bound: &'b TypeBound,
        self_ty: Ty,
        ignore_bindings: bool,
    ) -> impl Iterator<Item = Clause> + use<'b, 'a> {
        let mut trait_ref = None;
        let clause = match bound {
            TypeBound::Path(path, TraitBoundModifier::None) => {
                trait_ref = dbg!(self.lower_trait_ref_from_path(path, self_ty));
                trait_ref.clone().map(|trait_ref| Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Trait(TraitPredicate { trait_ref, polarity: rustc_type_ir::PredicatePolarity::Positive }))))))

            }
            TypeBound::Path(path, TraitBoundModifier::Maybe) => {
                let sized_trait = self
                    .db
                    .lang_item(self.resolver.krate(), LangItem::Sized)
                    .and_then(|lang_item| lang_item.as_trait());
                // Don't lower associated type bindings as the only possible relaxed trait bound
                // `?Sized` has no of them.
                // If we got another trait here ignore the bound completely.
                let trait_id = self
                    .lower_trait_ref_from_path(path, self_ty.clone())
                    .map(|trait_ref| trait_ref.def_id)
                    .map(|def_id| match def_id {
                        GenericDefId::TraitId(id) => id,
                        _ => unreachable!(),
                    });
                if trait_id == sized_trait {
                    self.unsized_types.insert(self_ty);
                }
                None
            }
            TypeBound::ForLifetime(_, path) => {
                // FIXME Don't silently drop the hrtb lifetimes here
                trait_ref = self.lower_trait_ref_from_path(path, self_ty);
                trait_ref.clone().map(|trait_ref| Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Trait(TraitPredicate { trait_ref, polarity: rustc_type_ir::PredicatePolarity::Positive }))))))
            }
            TypeBound::Lifetime(l) => {
                let lifetime = self.lower_lifetime(l);
                Some(Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::TypeOutlives(OutlivesPredicate(self_ty, lifetime)))))))
            }
            TypeBound::Use(_) | TypeBound::Error => None,
        };
        clause.into_iter().chain(
            trait_ref
                .filter(move |_| !ignore_bindings)
                .map(move |tr| self.assoc_type_bindings_from_type_bound(bound, tr))
                .into_iter()
                .flatten(),
        )
    }

    fn assoc_type_bindings_from_type_bound<'b>(
        &'b mut self,
        bound: &'b TypeBound,
        trait_ref: TraitRef,
    ) -> impl Iterator<Item = Clause> + use<'b, 'a> {
        let last_segment = match bound {
            TypeBound::Path(path, TraitBoundModifier::None) | TypeBound::ForLifetime(_, path) => {
                path.segments().last()
            }
            TypeBound::Path(_, TraitBoundModifier::Maybe)
            | TypeBound::Use(_)
            | TypeBound::Error
            | TypeBound::Lifetime(_) => None,
        };
        last_segment
            .into_iter()
            .filter_map(|segment| segment.args_and_bindings)
            .flat_map(|args_and_bindings| args_and_bindings.bindings.iter())
            .flat_map(move |binding| {
                let found = associated_type_by_name_including_super_traits(
                    self.db,
                    trait_ref.clone(),
                    &binding.name,
                );
                let (super_trait_ref, associated_ty) = match found {
                    None => return SmallVec::new(),
                    Some(t) => t,
                };
                // FIXME: `substs_from_path_segment()` pushes `TyKind::Error` for every parent
                // generic params. It's inefficient to splice the `Substitution`s, so we may want
                // that method to optionally take parent `Substitution` as we already know them at
                // this point (`super_trait_ref.substitution`).
                let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                let args = self.substs_from_path_segment(
                    // FIXME: This is hack. We shouldn't really build `PathSegment` directly.
                    PathSegment { name: &binding.name, args_and_bindings: binding.args.as_ref() },
                    Some(associated_ty.into()),
                    false, // this is not relevant
                    Some(super_trait_ref.self_ty()),
                );
                let self_params = generics(self.db.upcast(), associated_ty.into()).len_self();
                let args = GenericArgs::new_from_iter(
                    args
                        .iter()
                        .take(self_params)
                        .chain(super_trait_ref.args.iter()),
                );
                let projection_term = AliasTerm::new_from_args(fake_ir, associated_ty.into(), args.clone());
                let mut predicates: SmallVec<[_; 1]> = SmallVec::with_capacity(
                    binding.type_ref.as_ref().map_or(0, |_| 1) + binding.bounds.len(),
                );
                if let Some(type_ref) = binding.type_ref {
                    match (&self.types_map[type_ref], self.impl_trait_mode.mode) {
                        (TypeRef::ImplTrait(_), ImplTraitLoweringMode::Disallowed) => (),
                        (_, ImplTraitLoweringMode::Disallowed | ImplTraitLoweringMode::Opaque) => {
                            let ty = self.lower_ty(type_ref);
                            let pred = Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Projection(ProjectionPredicate {
                                projection_term,
                                term: ty.into(),
                            })))));
                            predicates.push(pred);
                        }
                        (_, ImplTraitLoweringMode::Param | ImplTraitLoweringMode::Variable) => {
                            // Find the generic index for the target of our `bound`
                            let target_param_idx = self
                                .resolver
                                .where_predicates_in_scope()
                                .find_map(|(p, _)| match p {
                                    WherePredicate::TypeBound {
                                        target: WherePredicateTypeTarget::TypeOrConstParam(idx),
                                        bound: b,
                                    } if b == bound => Some(idx),
                                    _ => None,
                                });
                            let ty = if let Some(target_param_idx) = target_param_idx {
                                let mut counter = 0;
                                let generics = self.generics().expect("generics in scope");
                                for (idx, data) in generics.iter_self_type_or_consts() {
                                    // Count the number of `impl Trait` things that appear before
                                    // the target of our `bound`.
                                    // Our counter within `impl_trait_mode` should be that number
                                    // to properly lower each types within `type_ref`
                                    if data.type_param().is_some_and(|p| {
                                        p.provenance == TypeParamProvenance::ArgumentImplTrait
                                    }) {
                                        counter += 1;
                                    }
                                    if idx == *target_param_idx {
                                        break;
                                    }
                                }
                                let mut ext = TyLoweringContext::new_maybe_unowned(
                                    self.db,
                                    self.resolver,
                                    self.types_map,
                                    self.types_source_map,
                                    self.owner,
                                )
                                .with_type_param_mode(self.type_param_mode);
                                match self.impl_trait_mode.mode {
                                    ImplTraitLoweringMode::Param => {
                                        ext.impl_trait_mode =
                                            ImplTraitLoweringState::param(counter);
                                    }
                                    ImplTraitLoweringMode::Variable => {
                                        ext.impl_trait_mode =
                                            ImplTraitLoweringState::variable(counter);
                                    }
                                    _ => unreachable!(),
                                }
                                ext.lower_ty(type_ref)
                            } else {
                                self.lower_ty(type_ref)
                            };

                            let pred = Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Projection(ProjectionPredicate {
                                projection_term,
                                term: ty.into(),
                            })))));
                            predicates.push(pred);
                        }
                    }
                }
                for bound in binding.bounds.iter() {
                    predicates.extend(self.lower_type_bound(
                        bound,
                        Ty::new_alias(DbInterner, AliasTyKind::Projection, AliasTy::new_from_args(fake_ir, associated_ty.into(), args.clone())),
                        false,
                    ));
                }
                predicates
            })
    }

    fn lower_dyn_trait(&mut self, bounds: &[TypeBound]) -> Ty {
        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
        let self_ty = Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::ZERO, kind: BoundTyKind::Anon });
        // INVARIANT: The principal trait bound, if present, must come first. Others may be in any
        // order but should be in the same order for the same set but possibly different order of
        // bounds in the input.
        // INVARIANT: If this function returns `DynTy`, there should be at least one trait bound.
        // These invariants are utilized by `TyExt::dyn_trait()` and chalk.
        let mut lifetime = None;
        let bounds = self.with_shifted_in(DebruijnIndex::from_u32(1), |ctx| {
            let mut lowered_bounds: Vec<rustc_type_ir::Binder<DbInterner, ExistentialPredicate<DbInterner>>> = Vec::new();
            for b in bounds {
                let db = ctx.db;
                ctx.lower_type_bound(b, self_ty.clone(), false).for_each(|b| {
                    if let Some(bound) = b.kind().map_bound(|c| match c {
                        rustc_type_ir::ClauseKind::Trait(t) => {
                            let id = t.def_id();
                            let id = match id {
                                GenericDefId::TraitId(id) => id,
                                _ => unreachable!(),
                            };
                            let is_auto = db.trait_data(id).is_auto;
                            if is_auto {
                                Some(ExistentialPredicate::AutoTrait(t.def_id()))
                            } else {
                                Some(ExistentialPredicate::Trait(ExistentialTraitRef::new_from_args(fake_ir, t.def_id(), GenericArgs::new_from_iter(t.trait_ref.args.iter().skip(1)))))
                            }
                        }
                        rustc_type_ir::ClauseKind::Projection(p) => {
                            Some(ExistentialPredicate::Projection(ExistentialProjection::new_from_args(fake_ir, p.def_id(), GenericArgs::new_from_iter(p.projection_term.args.iter().skip(1)), p.term)))
                        }
                        rustc_type_ir::ClauseKind::TypeOutlives(outlives_predicate) => {
                            lifetime = Some(outlives_predicate.1);
                            None
                        }
                        rustc_type_ir::ClauseKind::RegionOutlives(_)
                        | rustc_type_ir::ClauseKind::ConstArgHasType(_, _)
                        | rustc_type_ir::ClauseKind::WellFormed(_)
                        | rustc_type_ir::ClauseKind::ConstEvaluatable(_)
                        | rustc_type_ir::ClauseKind::HostEffect(_) => unreachable!(),
                    }).transpose() {
                        lowered_bounds.push(bound);
                    }
                })
            }

            let mut multiple_regular_traits = false;
            let mut multiple_same_projection = false;
            lowered_bounds.sort_unstable_by(|lhs, rhs| {
                use std::cmp::Ordering;
                match (lhs.clone().skip_binder(), rhs.clone().skip_binder()) {
                    (ExistentialPredicate::Trait(_), ExistentialPredicate::Trait(_)) => {
                        multiple_regular_traits = true;
                        // Order doesn't matter - we error
                        Ordering::Equal
                    }
                    (ExistentialPredicate::AutoTrait(lhs_id), ExistentialPredicate::AutoTrait(rhs_id)) => {
                        let lhs_id = match lhs_id {
                            GenericDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        let rhs_id = match rhs_id {
                            GenericDefId::TraitId(id) => id,
                            _ => unreachable!(),
                        };
                        lhs_id.cmp(&rhs_id)
                    }
                    (ExistentialPredicate::Trait(_), _) => Ordering::Less,
                    (_, ExistentialPredicate::Trait(_)) => Ordering::Greater,
                    (ExistentialPredicate::AutoTrait(_), _) => Ordering::Less,
                    (_, ExistentialPredicate::AutoTrait(_)) => Ordering::Greater,
                    (ExistentialPredicate::Projection(lhs), ExistentialPredicate::Projection(rhs)) => {
                        let lhs_id = match lhs.def_id {
                            GenericDefId::TypeAliasId(id) => id,
                            _ => unreachable!(),
                        };
                        let rhs_id = match rhs.def_id {
                            GenericDefId::TypeAliasId(id) => id,
                            _ => unreachable!(),
                        };
                        // We only compare the `associated_ty_id`s. We shouldn't have
                        // multiple bounds for an associated type in the correct Rust code,
                        // and if we do, we error out.
                        if lhs_id == rhs_id {
                            multiple_same_projection = true;
                        }
                        use base_db::ra_salsa::InternKey;
                        lhs_id.as_intern_id().cmp(&rhs_id.as_intern_id())
                    }
                }
            });

            if multiple_regular_traits || multiple_same_projection {
                return None;
            }

            if !lowered_bounds.first().map_or( false, |b| matches!(b.as_ref().skip_binder(), ExistentialPredicate::Trait(_) | ExistentialPredicate::AutoTrait(_))) {
                return None;
            }

            // As multiple occurrences of the same auto traits *are* permitted, we deduplicate the
            // bounds. We shouldn't have repeated elements besides auto traits at this point.
            lowered_bounds.dedup();

            Some(BoundExistentialPredicates::new_from_iter(lowered_bounds))
        });

        if let Some(bounds) = bounds {
            let region = match lifetime {
                Some(it) => match it.clone().kind() {
                    rustc_type_ir::RegionKind::ReBound(db, var) => Region::new_bound(DbInterner, db.shifted_out_to_binder(DebruijnIndex::from_u32(2)), var),
                    _ => it,
                }
                None => Region::new_static(DbInterner),
            };
            Ty::new_dynamic(DbInterner, bounds, region, rustc_type_ir::DynKind::Dyn)
        } else {
            // FIXME: report error
            // (additional non-auto traits, associated type rebound, or no resolved trait)
            Ty::new_error(DbInterner, ErrorGuaranteed)
        }
    }

    fn lower_impl_trait(&mut self, bounds: &[TypeBound], krate: CrateId) -> Vec<Clause> {
        let fake_ir = crate::next_solver::DbIr::new(self.db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
        cov_mark::hit!(lower_rpit);
        let self_ty = Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::ZERO, kind: BoundTyKind::Anon });
        let predicates = self.with_shifted_in(DebruijnIndex::from_u32(1), |ctx| {
            let mut predicates = Vec::new();
            for b in bounds {
                predicates.extend(ctx.lower_type_bound(b, self_ty.clone(), false));
            }

            if !ctx.unsized_types.contains(&self_ty) {
                let sized_trait = ctx
                    .db
                    .lang_item(krate, LangItem::Sized);
                let sized_clause = sized_trait.map(|trait_id| {
                    let trait_ref = TraitRef::new_from_args(fake_ir, trait_id.as_trait().unwrap().into(), GenericArgs::new_from_iter([self_ty.clone().into()]));
                    Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Trait(TraitPredicate { trait_ref, polarity: rustc_type_ir::PredicatePolarity::Positive })))))
                });
                predicates.extend(sized_clause);
            }
            predicates.shrink_to_fit();
            predicates
        });
        predicates
    }

    pub fn lower_lifetime(&self, lifetime: &LifetimeRef) -> Region {
        match self.resolver.resolve_lifetime(lifetime) {
            Some(resolution) => match resolution {
                LifetimeNs::Static => Region::new_static(DbInterner),
                LifetimeNs::LifetimeParam(id) => match self.type_param_mode {
                    ParamLoweringMode::Placeholder => {
                        let interned_id = self.db.intern_lifetime_param_id(id);
                        let var = base_db::ra_salsa::InternKey::as_intern_id(&interned_id).as_usize();
                        Region::new_placeholder(Placeholder::new(UniverseIndex::ROOT, rustc_type_ir::BoundVar::from_usize(var)))
                    }
                    ParamLoweringMode::Variable => {
                        let generics = self.generics().expect("generics in scope");
                        let idx = match generics.lifetime_idx(id) {
                            None => return Region::error(),
                            Some(idx) => idx,
                        };
                        let bound = BoundRegion {
                            var: rustc_type_ir::BoundVar::from_usize(idx),
                            kind: BoundRegionKind::Anon,
                        };
                        Region::new_bound(DbInterner, DebruijnIndex::from_u32(self.in_binders.as_u32()), bound)
                    }
                    ParamLoweringMode::Param => {
                        let generics = self.generics().expect("generics in scope");
                        let idx = match generics.lifetime_idx(id) {
                            None => return Region::error(),
                            Some(idx) => idx,
                        };
                        Region::new_early_param(EarlyParamRegion { index: idx as u32, name: sym::MISSING_NAME.clone()})
                    }
                }
            },
            None => Region::error(),
        }
    }

    // FIXME: This does not handle macros!
    fn count_impl_traits(&self, type_ref: TypeRefId) -> usize {
        let mut count = 0;
        TypeRef::walk(type_ref, self.types_map, &mut |type_ref| {
            if matches!(type_ref, TypeRef::ImplTrait(_)) {
                count += 1;
            }
        });
        count
    }
}

fn named_associated_type_shorthand_candidates(
    db: &dyn HirDatabase,
    // If the type parameter is defined in an impl and we're in a method, there
    // might be additional where clauses to consider
    def: GenericDefId,
    res: TypeNs,
    assoc_name: Option<Name>,
    // Do NOT let `cb` touch `TraitRef` outside of `TyLoweringContext`. Its substitution contains
    // free `BoundVar`s that need to be shifted and only `TyLoweringContext` knows how to do that
    // properly (see `TyLoweringContext::select_associated_type()`).
    mut cb: impl FnMut(&Name, &TraitRef, TypeAliasId) -> Option<Ty>,
) -> Option<Ty> {
    let mut search = |t| {
        all_super_trait_refs(db, t, |t| {
            let trait_id = match t.def_id {
                GenericDefId::TraitId(id) => id,
                _ => unreachable!(),
            };
            let data = db.trait_data(trait_id);

            for (name, assoc_id) in &data.items {
                if let AssocItemId::TypeAliasId(alias) = assoc_id {
                    if let Some(result) = cb(name, &t, *alias) {
                        return Some(result);
                    }
                }
            }
            None
        })
    };

    match res {
        TypeNs::SelfType(impl_id) => {
            // we're _in_ the impl -- the binders get added back later. Correct,
            // but it would be nice to make this more explicit
            // FIXME: use db query
            let trait_ref = impl_trait_query(db, impl_id)?;

            let impl_id_as_generic_def: GenericDefId = impl_id.into();
            if impl_id_as_generic_def != def {
                // `trait_ref` contains `BoundVar`s bound by impl's `Binders`, but here we need
                // `BoundVar`s from `def`'s point of view.
                // FIXME: A `HirDatabase` query may be handy if this process is needed in more
                // places. It'd be almost identical as `impl_trait_query` where `resolver` would be
                // of `def` instead of `impl_id`.
                let starting_idx = generics(db.upcast(), def).len_self();

                let generics = generics(db.upcast(), def.into());
                assert!(generics.parent_generics().is_none());
                let params = generics
                    .iter_self()
                    .map(|(id, _data)| match id {
                        GenericParamId::TypeParamId(_) => ParamKind::Type,
                        GenericParamId::ConstParamId(id) => ParamKind::Const(db.const_param_ty(id)),
                        GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
                    });

                let args = GenericArgs::new_from_iter((starting_idx..).zip(params).map(|(idx, kind)| match kind {
                    ParamKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_usize(idx), kind: BoundTyKind::Anon }).into(),
                    ParamKind::Const(_) => {
                        Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_usize(idx)).into()
                    }
                    ParamKind::Lifetime => {
                        Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion { var: BoundVar::from_usize(idx), kind: BoundRegionKind::Anon }).into()
                    }
                }));

                let trait_ref = apply_args_to_binder(trait_ref, args, db);
                search(trait_ref)
            } else {
                search(trait_ref.skip_binder())
            }
        }
        TypeNs::GenericParam(param_id) => {
            let predicates = generic_predicates_for_param_query(db, def, param_id.into(), assoc_name);
            let res = predicates.iter().find_map(|pred| match pred.clone().kind().skip_binder() {
                rustc_type_ir::ClauseKind::Trait(trait_predicate) => {
                    let trait_ref = trait_predicate.trait_ref;
                    assert!(!trait_ref.has_escaping_bound_vars(), "FIXME unexpected higher-ranked trait bound");
                    search(trait_ref)
                }
                _ => None,
            });
            if res.is_some() {
                return res;
            }
            // Handle `Self::Type` referring to own associated type in trait definitions
            if let GenericDefId::TraitId(trait_id) = param_id.parent() {
                let trait_generics = generics(db.upcast(), trait_id.into());
                if trait_generics[param_id.local_id()].is_trait_self() {
                    let def_generics = generics(db.upcast(), def);
                    let starting_idx = match def {
                        GenericDefId::TraitId(_) => 0,
                        // `def` is an item within trait. We need to substitute `BoundVar`s but
                        // remember that they are for parent (i.e. trait) generic params so they
                        // come after our own params.
                        _ => def_generics.len_self(),
                    };
                    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                    let args = GenericArgs::for_item(fake_ir, trait_id.into(), |param, _| match param.kind {
                        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_u32(param.index()), kind: BoundTyKind::Anon }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion { var: BoundVar::from_u32(param.index()), kind: BoundRegionKind::Anon }).into(),
                        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_u32(param.index())).into(),
                    });
                    let trait_ref = TraitRef::new_from_args(fake_ir, trait_id.into(), args);
                    return search(trait_ref);
                }
            }
            None
        }
        _ => None,
    }
}

pub(crate) fn lower_mutability(m: hir_def::type_ref::Mutability) -> Mutability {
    match m {
        hir_def::type_ref::Mutability::Shared => Mutability::Not,
        hir_def::type_ref::Mutability::Mut => Mutability::Mut,
    }
}

pub(crate) fn const_or_path_to_const<'g>(
    db: &dyn HirDatabase,
    resolver: &Resolver,
    owner: TypeOwnerId,
    expected_ty: Ty,
    value: &ConstRef,
    mode: ParamLoweringMode,
    args: impl FnOnce() -> Option<&'g Generics>,
    debruijn: DebruijnIndex,
) -> Const {
    // FIXME: needs next-solver types all the way down
    unknown_const(expected_ty)
    /*
    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    match value {
        ConstRef::Scalar(s) => intern_const_ref(db, s, expected_ty, resolver.krate()),
        ConstRef::Path(n) => {
            let path = ModPath::from_segments(PathKind::Plain, Some(n.clone()));
            path_to_const(
                db,
                resolver,
                &Path::from_known_path_with_no_generic(path),
                mode,
                args,
                debruijn,
                expected_ty.clone(),
            )
            .map(|c| c.to_nextsolver(fake_ir))
            .unwrap_or_else(|| unknown_const(expected_ty))
        }
        &ConstRef::Complex(it) => {
            let crate_data = &db.crate_graph()[resolver.krate()];
            if crate_data.env.get("__ra_is_test_fixture").is_none() && crate_data.origin.is_local()
            {
                // FIXME: current `InTypeConstId` is very unstable, so we only use it in non local crate
                // that are unlikely to be edited.
                return unknown_const(expected_ty);
            }
            let c = db
                .intern_in_type_const(InTypeConstLoc {
                    id: it,
                    owner,
                    expected_ty: Box::new(InTypeConstIdMetadata(expected_ty.clone())),
                })
                .into();
            Const::new(ConstKind::Value(expected_ty, ValueConst::new(ConstScalar::UnevaluatedConst(c, chalk_ir::Substitution::empty(crate::Interner)))))
        }
    }
    */
}


fn unknown_const(ty: Ty) -> Const {
    Const::new(ConstKind::Value(ty, ValueConst::new(ConstScalar::Unknown)))
}


pub(crate) fn impl_trait_query(db: &dyn HirDatabase, impl_id: ImplId) -> Option<Binder<TraitRef>> {
    let impl_data = db.impl_data(impl_id);
    let resolver = impl_id.resolver(db.upcast());
    let mut ctx = TyLoweringContext::new(db, &resolver, &impl_data.types_map, impl_id.into())
        .with_type_param_mode(ParamLoweringMode::Variable);
    // FIXME: use db query
    let self_ty = impl_self_ty_query(db, impl_id);
    let target_trait = impl_data.target_trait.as_ref()?;
    let trait_ref = ctx.lower_trait_ref(target_trait, self_ty.clone().skip_binder())?;
    Some(Binder::bind_with_vars(trait_ref, self_ty.bound_vars()))
}

pub(crate) fn impl_self_ty_query(db: &dyn HirDatabase, impl_id: ImplId) -> Binder<Ty> {
    let impl_data = db.impl_data(impl_id);
    let resolver = impl_id.resolver(db.upcast());
    let generics = generics(db.upcast(), impl_id.into());
    let mut ctx = TyLoweringContext::new(db, &resolver, &impl_data.types_map, impl_id.into())
        .with_type_param_mode(ParamLoweringMode::Variable);
    make_binders(&generics, ctx.lower_ty(impl_data.self_ty))
}

// `generic_predicates_for_param` hits cycles for some tests (anything with minicore's `Try`). In salsa, this query cycle
// is recovered. We're just gonna...cheat. This could be wrong, it's a big hack and it's going away. Just don't want to
// have to ignore a bunch of tests or disable functionality.
static REENTRANT_QUERY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// This query exists only to be used when resolving short-hand associated types
/// like `T::Item`.
///
/// See the analogous query in rustc and its comment:
/// <https://github.com/rust-lang/rust/blob/9150f844e2624eb013ec78ca08c1d416e6644026/src/librustc_typeck/astconv.rs#L46>
/// This is a query mostly to handle cycles somewhat gracefully; e.g. the
/// following bounds are disallowed: `T: Foo<U::Item>, U: Foo<T::Item>`, but
/// these are fine: `T: Foo<U::Item>, U: Foo<()>`.
pub(crate) fn generic_predicates_for_param_query(
    db: &dyn HirDatabase,
    def: GenericDefId,
    param_id: TypeOrConstParamId,
    assoc_name: Option<Name>,
) -> GenericPredicates {
    if REENTRANT_QUERY.swap(true, std::sync::atomic::Ordering::AcqRel) {
        return GenericPredicates(None);
    }
    let resolver = def.resolver(db.upcast());
    let mut ctx = if let GenericDefId::FunctionId(_) = def {
        TyLoweringContext::new(db, &resolver, TypesMap::EMPTY, def.into())
            .with_impl_trait_mode(ImplTraitLoweringMode::Variable)
            .with_type_param_mode(ParamLoweringMode::Variable)
    } else {
        TyLoweringContext::new(db, &resolver, TypesMap::EMPTY, def.into())
            .with_type_param_mode(ParamLoweringMode::Variable)
    };
    let generics = generics(db.upcast(), def);

    // we have to filter out all other predicates *first*, before attempting to lower them
    let predicate = |pred: &_, def: &_, ctx: &mut TyLoweringContext<'_>| match pred {
        WherePredicate::ForLifetime { target, bound, .. }
        | WherePredicate::TypeBound { target, bound, .. } => {
            let invalid_target = match target {
                WherePredicateTypeTarget::TypeRef(type_ref) => {
                    ctx.lower_ty_only_param(*type_ref) != Some(param_id)
                }
                &WherePredicateTypeTarget::TypeOrConstParam(local_id) => {
                    let target_id = TypeOrConstParamId { parent: *def, local_id };
                    target_id != param_id
                }
            };
            if invalid_target {
                // If this is filtered out without lowering, `?Sized` is not gathered into `ctx.unsized_types`
                if let TypeBound::Path(_, TraitBoundModifier::Maybe) = bound {
                    ctx.lower_where_predicate(pred, def, true).for_each(drop);
                }
                return false;
            }

            match bound {
                TypeBound::ForLifetime(_, path) | TypeBound::Path(path, _) => {
                    // Only lower the bound if the trait could possibly define the associated
                    // type we're looking for.

                    let Some(assoc_name) = &assoc_name else { return true };
                    let Some(TypeNs::TraitId(tr)) =
                        resolver.resolve_path_in_type_ns_fully(db.upcast(), path)
                    else {
                        return false;
                    };

                    all_super_traits(db.upcast(), tr).iter().any(|tr| {
                        db.trait_data(*tr).items.iter().any(|(name, item)| {
                            matches!(item, AssocItemId::TypeAliasId(_)) && name == assoc_name
                        })
                    })
                }
                TypeBound::Use(_) | TypeBound::Lifetime(_) | TypeBound::Error => false,
            }
        }
        WherePredicate::Lifetime { .. } => false,
    };
    let mut predicates = Vec::new();
    for (params, def) in resolver.all_generic_params() {
        ctx.types_map = &params.types_map;
        for pred in params.where_predicates() {
            if predicate(pred, def, &mut ctx) {
                predicates.extend(
                    ctx.lower_where_predicate(pred, def, true)
                );
            }
        }
    }

    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let args = GenericArgs::for_item(fake_ir, def, |param, _| match param.kind {
        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var: BoundVar::from_u32(param.index()), kind: BoundTyKind::Anon }).into(),
        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_bound(DbInterner, DebruijnIndex::ZERO, BoundRegion { var: BoundVar::from_u32(param.index()), kind: BoundRegionKind::Anon }).into(),
        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_bound(DbInterner, DebruijnIndex::ZERO, BoundVar::from_u32(param.index())).into(),
    });
    if !args.clone().is_empty() {
        let explicitly_unsized_tys = ctx.unsized_types;
        if let Some(implicitly_sized_predicates) = implicitly_sized_clauses(
            db,
            param_id.parent,
            &explicitly_unsized_tys,
            &args,
            &resolver,
        ) {
            predicates.extend(implicitly_sized_predicates);
        };
    }
    REENTRANT_QUERY.swap(false,std::sync::atomic::Ordering::AcqRel);
    GenericPredicates(predicates.is_empty().not().then(|| predicates.into()))
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericPredicates(Option<Arc<[Clause]>>);

impl ops::Deref for GenericPredicates {
    type Target = [Clause];

    fn deref(&self) -> &Self::Target {
        self.0.as_deref().unwrap_or(&[])
    }
}

/// Resolve the where clause(s) of an item with generics.
pub(crate) fn generic_predicates_query(
    db: &dyn HirDatabase,
    def: GenericDefId,
) -> GenericPredicates {
    generic_predicates_filtered_by(db, def, |_, _| true)
}

/// Resolve the where clause(s) of an item with generics,
/// except the ones inherited from the parent
pub(crate) fn generic_predicates_without_parent_query(
    db: &dyn HirDatabase,
    def: GenericDefId,
) -> GenericPredicates {
    generic_predicates_filtered_by(db, def, |_, d| *d == def)
}

/// Resolve the where clause(s) of an item with generics,
/// with a given filter
pub(crate) fn generic_predicates_filtered_by<F>(
    db: &dyn HirDatabase,
    def: GenericDefId,
    filter: F,
) -> GenericPredicates
where
    F: Fn(&WherePredicate, &GenericDefId) -> bool,
{
    let resolver = def.resolver(db.upcast());
    let (impl_trait_lowering, param_lowering) = match def {
        GenericDefId::FunctionId(_) => {
            (ImplTraitLoweringMode::Variable, ParamLoweringMode::Param)
        }
        _ => (ImplTraitLoweringMode::Disallowed, ParamLoweringMode::Param),
    };
    let mut ctx = TyLoweringContext::new(db, &resolver, TypesMap::EMPTY, def.into())
        .with_impl_trait_mode(impl_trait_lowering)
        .with_type_param_mode(param_lowering);

    let mut predicates = Vec::new();
    for (params, def) in resolver.all_generic_params() {
        ctx.types_map = &params.types_map;
        for pred in params.where_predicates() {
            if filter(pred, def) {
                predicates.extend(
                    ctx.lower_where_predicate(pred, def, false),
                );
            }
        }
    }

    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let args = GenericArgs::for_item(fake_ir, def, |param, _| match param.kind {
        crate::next_solver::generics::GenericParamDefKind::Type => Ty::new_param(param.index(), param.name.clone()).into(),
        crate::next_solver::generics::GenericParamDefKind::Lifetime => Region::new_early_param(EarlyParamRegion { index: param.index(), name: param.name.clone() }).into(),
        crate::next_solver::generics::GenericParamDefKind::Const => Const::new_param(ParamConst { index: param.index(), name: param.name.clone() }).into(),
    });
    if args.len() > 0 {
        let explicitly_unsized_tys = ctx.unsized_types;
        if let Some(implicitly_sized_predicates) =
            implicitly_sized_clauses(db, def, &explicitly_unsized_tys, &args, &resolver)
        {
            predicates.extend(
                implicitly_sized_predicates
            );
        };
    }
    GenericPredicates(predicates.is_empty().not().then(|| predicates.into()))
}

/// Generate implicit `: Sized` predicates for all generics that has no `?Sized` bound.
/// Exception is Self of a trait def.
fn implicitly_sized_clauses<'a, 'subst: 'a>(
    db: &'a dyn HirDatabase,
    def: GenericDefId,
    explicitly_unsized_tys: &'a FxHashSet<Ty>,
    args: &'subst GenericArgs,
    resolver: &Resolver,
) -> Option<impl Iterator<Item = Clause> + Captures<'a> + Captures<'subst>> {
    let sized_trait = db
        .lang_item(resolver.krate(), LangItem::Sized)
        .and_then(|lang_item| lang_item.as_trait())?;

    let trait_self_idx = trait_self_param_idx(db.upcast(), def);

    Some(
        args
            .iter()
            .enumerate()
            .filter_map(
                move |(idx, generic_arg)| {
                    if Some(idx) == trait_self_idx {
                        None
                    } else {
                        Some(generic_arg)
                    }
                },
            )
            .filter_map(|generic_arg| generic_arg.as_type())
            .filter(move |self_ty| !explicitly_unsized_tys.contains(self_ty))
            .map(move |self_ty| {
                let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
                let trait_ref = TraitRef::new_from_args(fake_ir, sized_trait.into(), GenericArgs::new_from_iter([self_ty.into()]));
                Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(rustc_type_ir::ClauseKind::Trait(TraitPredicate { trait_ref, polarity: rustc_type_ir::PredicatePolarity::Positive })))))
            }),
    )
}

pub(crate) fn make_single_type_binders<T: rustc_type_ir::visit::TypeVisitable<DbInterner>>(
    value: T,
) -> Binder<T> {
    Binder::bind_with_vars(
        value,
        BoundVarKinds::new_from_iter([BoundVarKind::Ty(BoundTyKind::Anon)]),
    )
}

pub(crate) fn make_binders<T: rustc_type_ir::visit::TypeVisitable<DbInterner>>(
    generics: &Generics,
    value: T,
) -> Binder<T> {
    Binder::bind_with_vars(
        value,
        BoundVarKinds::new_from_iter(generics.iter_id().map(|x| match x {
            hir_def::GenericParamId::ConstParamId(_) => {
                BoundVarKind::Const
            }
            hir_def::GenericParamId::TypeParamId(_) => {
                BoundVarKind::Ty(BoundTyKind::Anon)
            }
            hir_def::GenericParamId::LifetimeParamId(_) => BoundVarKind::Region(BoundRegionKind::Anon),
        })),
    )
}

/// Checks if the provided generic arg matches its expected kind, then lower them via
/// provided closures. Use unknown if there was kind mismatch.
///
pub(crate) fn lower_generic_arg<'a, T>(
    db: &dyn HirDatabase,
    kind_id: GenericParamId,
    arg: &'a GenericArg,
    this: &mut T,
    types_map: &TypesMap,
    for_type: impl FnOnce(&mut T, TypeRefId) -> Ty + 'a,
    for_const: impl FnOnce(&mut T, &ConstRef, Ty) -> Const + 'a,
    for_lifetime: impl FnOnce(&mut T, &LifetimeRef) -> Region + 'a,
) -> crate::next_solver::GenericArg {
    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let kind = match kind_id {
        GenericParamId::TypeParamId(_) => ParamKind::Type,
        GenericParamId::ConstParamId(id) => {
            let ty = db.const_param_ty(id);
            ParamKind::Const(ty)
        }
        GenericParamId::LifetimeParamId(_) => ParamKind::Lifetime,
    };
    match (arg, kind) {
        (GenericArg::Type(type_ref), ParamKind::Type) => for_type(this, *type_ref).into(),
        (GenericArg::Const(c), ParamKind::Const(c_ty)) => for_const(this, c, c_ty.to_nextsolver(fake_ir)).into(),
        (GenericArg::Lifetime(lifetime_ref), ParamKind::Lifetime) => {
            for_lifetime(this, lifetime_ref).into()
        }
        (GenericArg::Const(_), ParamKind::Type) => Ty::new_error(DbInterner, ErrorGuaranteed).into(),
        (GenericArg::Lifetime(_), ParamKind::Type) => Ty::new_error(DbInterner, ErrorGuaranteed).into(),
        (GenericArg::Type(t), ParamKind::Const(c_ty)) => {
            // We want to recover simple idents, which parser detects them
            // as types. Maybe here is not the best place to do it, but
            // it works.
            if let TypeRef::Path(p) = &types_map[*t] {
                if let Some(p) = p.mod_path() {
                    if p.kind == PathKind::Plain {
                        if let [n] = p.segments() {
                            let c = ConstRef::Path(n.clone());
                            return for_const(this, &c, c_ty.to_nextsolver(fake_ir)).into();
                        }
                    }
                }
            }
            unknown_const(c_ty.to_nextsolver(fake_ir)).into()
        }
        (GenericArg::Lifetime(_), ParamKind::Const(c_ty)) => unknown_const(c_ty.to_nextsolver(fake_ir)).into(),
        (GenericArg::Type(_), ParamKind::Lifetime) => Region::error().into(),
        (GenericArg::Const(_), ParamKind::Lifetime) => Region::error().into(),
    }
}

/// Build the signature of a callable item (function, struct or enum variant).
pub(crate) fn callable_item_sig(db: &dyn HirDatabase, def: CallableDefId) -> EarlyBinder<PolyFnSig> {
    match def {
        CallableDefId::FunctionId(f) => fn_sig_for_fn(db, f),
        CallableDefId::StructId(s) => fn_sig_for_struct_constructor(db, s),
        CallableDefId::EnumVariantId(e) => fn_sig_for_enum_variant_constructor(db, e),
    }
}

fn fn_sig_for_fn(db: &dyn HirDatabase, def: FunctionId) -> EarlyBinder<PolyFnSig> {
    let data = db.function_data(def);
    let resolver = def.resolver(db.upcast());
    let mut ctx_params = TyLoweringContext::new(db, &resolver, &data.types_map, def.into())
        .with_impl_trait_mode(ImplTraitLoweringMode::Variable)
        .with_type_param_mode(ParamLoweringMode::Variable);
    let params = data.params.iter().map(|&tr| ctx_params.lower_ty(tr));
    let mut ctx_ret = TyLoweringContext::new(db, &resolver, &data.types_map, def.into())
        .with_impl_trait_mode(ImplTraitLoweringMode::Opaque)
        .with_type_param_mode(ParamLoweringMode::Variable);
    let ret = ctx_ret.lower_ty(data.ret_type);
    let generics = generics(db.upcast(), def.into());

    let inputs_and_output = Tys::new_from_iter(params.chain(Some(ret)));
    EarlyBinder::bind(make_binders(&generics, FnSig {
        abi: data.abi.as_ref().map_or(FnAbi::Rust, FnAbi::from_symbol),
        c_variadic: data.is_varargs(),
        safety: if data.is_unsafe() { Safety::Unsafe } else { Safety::Safe },
        inputs_and_output,
    }))
}

fn type_for_adt(db: &dyn HirDatabase, adt: AdtId) -> EarlyBinder<Ty> {
    let generics = generics(db.upcast(), adt.into());
    let fake_ir = crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let args = generics.bound_vars_subst(db, chalk_ir::DebruijnIndex::INNERMOST).to_nextsolver(fake_ir);
    let ty = Ty::new_adt(DbInterner, AdtDef::new(adt.into(), db), args);
    convert_binder_to_early_binder(make_binders(&generics, ty))
}


fn fn_sig_for_struct_constructor(db: &dyn HirDatabase, def: StructId) -> EarlyBinder<PolyFnSig> {
    let struct_data = db.struct_data(def);
    let fields = struct_data.variant_data.fields();
    let resolver = def.resolver(db.upcast());
    let mut ctx = TyLoweringContext::new(
        db,
        &resolver,
        struct_data.variant_data.types_map(),
        AdtId::from(def).into(),
    )
    .with_type_param_mode(ParamLoweringMode::Variable);
    let generics = generics(db.upcast(), def.into());
    let params = fields.iter().map(|(_, field)| convert_binder_to_early_binder(make_binders(&generics, ctx.lower_ty(field.type_ref))).skip_binder());
    let ret = type_for_adt(db, def.into()).skip_binder();

    let inputs_and_output = Tys::new_from_iter(params.chain(Some(ret)));
    EarlyBinder::bind(Binder::dummy(FnSig {
        abi: FnAbi::RustCall,
        c_variadic: false,
        safety: Safety::Safe,
        inputs_and_output,
    }))
}

fn fn_sig_for_enum_variant_constructor(db: &dyn HirDatabase, def: EnumVariantId) -> EarlyBinder<PolyFnSig> {
    let var_data = db.enum_variant_data(def);
    let fields = var_data.variant_data.fields();
    let resolver = def.resolver(db.upcast());
    let mut ctx = TyLoweringContext::new(
        db,
        &resolver,
        var_data.variant_data.types_map(),
        DefWithBodyId::VariantId(def).into(),
    )
    .with_type_param_mode(ParamLoweringMode::Variable);
    let generics = generics(db.upcast(), def.lookup(db.upcast()).parent.into());
    let params = fields.iter().map(|(_, field)| convert_binder_to_early_binder(make_binders(&generics, ctx.lower_ty(field.type_ref))).skip_binder());
    let ret = type_for_adt(db, def.lookup(db.upcast()).parent.into()).skip_binder();

    let inputs_and_output = Tys::new_from_iter(params.chain(Some(ret)));
    EarlyBinder::bind(Binder::dummy(FnSig {
        abi: FnAbi::RustCall,
        c_variadic: false,
        safety: Safety::Safe,
        inputs_and_output,
    }))
}
