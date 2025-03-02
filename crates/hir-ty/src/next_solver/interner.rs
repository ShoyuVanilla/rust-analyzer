#![allow(unused)]

use base_db::{ra_salsa::InternKey, CrateId};
use chalk_ir::{ProgramClauseImplication, SeparatorTraitRef};
use hir_def::data::adt::{FieldData, StructFlags};
use hir_def::data::TraitFlags;
use hir_def::lang_item::LangItem;
use hir_def::Lookup;
use hir_def::{hir::PatId, AdtId, BlockId, GenericDefId, TypeAliasId, VariantId};
use hir_def::{CallableDefId, EnumVariantId, ItemContainerId, OpaqueTyLoc, StructId, UnionId};
use intern::{impl_internable, sym, Interned};
use la_arena::Idx;
use rustc_abi::{ReprFlags, ReprOptions};
use rustc_hashes::Hash64;
use rustc_type_ir::elaborate::elaborate;
use rustc_type_ir::inherent::{
    AdtDef as _, GenericsOf, IntoKind, IrGenericArgs, SliceLike, Span as _,
};
use rustc_type_ir::{
    AliasTerm, AliasTermKind, AliasTy, EarlyBinder, ImplPolarity, InferTy, ProjectionPredicate,
    TraitPredicate, TraitRef,
};
use smallvec::{smallvec, SmallVec};
use std::fmt;
use std::ops::ControlFlow;
use triomphe::Arc;

use rustc_ast_ir::visit::VisitorResult;
use rustc_index_in_tree::{bit_set::BitSet, IndexVec};
use rustc_type_ir::visit::TypeVisitableExt;
use rustc_type_ir::{
    elaborate, fold,
    inherent::{self, Const as _, Region as _, Ty as _},
    ir_print, relate,
    solve::Reveal,
    visit, BoundVar, CollectAndApply, DebruijnIndex, GenericArgKind, RegionKind, RustIr, TermKind,
    UniverseIndex, Variance, WithCachedTypeInfo,
};

use crate::lower::generic_predicates_filtered_by;
use crate::lower_nextsolver::{
    self, callable_item_sig, field_types_query, generic_predicates_query,
    generic_predicates_without_parent_query, impl_trait_query, return_type_impl_traits, ty_query,
    type_alias_impl_traits, TyLoweringContext,
};
use crate::method_resolution::{TyFingerprint, ALL_FLOAT_FPS, ALL_INT_FPS};
use crate::next_solver::util::for_trait_impls;
use crate::next_solver::FxIndexMap;
use crate::{db::HirDatabase, interner::InternedWrapper, ConstScalar, FnAbi, Interner};

use super::generics::generics;
use super::util::sized_constraint_for_ty;
use super::ClauseKind;
use super::{
    abi::Safety,
    fold::{BoundVarReplacer, BoundVarReplacerDelegate, FnMutDelegate},
    generics::Generics,
    mapping::ChalkToNextSolver,
    region::{
        BoundRegion, BoundRegionKind, EarlyParamRegion, LateParamRegion, PlaceholderRegion, Region,
    },
    Binder, BoundExistentialPredicate, BoundExistentialPredicates, BoundTy, BoundTyKind,
    CanonicalVarInfo, Clause, Clauses, Const, ConstKind, DefiningOpaqueTypes, ErrorGuaranteed,
    ExprConst, ExternalConstraints, ExternalConstraintsData, GenericArg, GenericArgs,
    InternedClausesWrapper, ParamConst, ParamEnv, ParamTy, PlaceholderConst, PlaceholderTy,
    PredefinedOpaques, PredefinedOpaquesData, Predicate, PredicateKind, Term, Ty, TyKind, Tys,
    ValueConst,
};

impl_internable!(
    InternedWrapper<WithCachedTypeInfo<ConstKind>>,
    InternedWrapper<RegionKind<DbInterner>>,
    InternedWrapper<WithCachedTypeInfo<TyKind>>,
    InternedWrapper<WithCachedTypeInfo<Binder<PredicateKind>>>,
    InternedWrapper<SmallVec<[BoundExistentialPredicate; 2]>>,
    InternedWrapper<SmallVec<[BoundVarKind; 2]>>,
    InternedClausesWrapper,
    InternedWrapper<SmallVec<[GenericArg; 2]>>,
    InternedWrapper<SmallVec<[Ty; 2]>>,
    InternedWrapper<SmallVec<[CanonicalVarInfo; 2]>>,
    InternedWrapper<SmallVec<[GenericDefId; 2]>>,
    InternedWrapper<SmallVec<[Variance; 2]>>,
    InternedWrapper<PredefinedOpaquesData>,
    InternedWrapper<ExternalConstraintsData>,
);

#[macro_export]
#[doc(hidden)]
macro_rules! _interned_vec {
    ($name:ident, $ty:ty) => {
        paste::paste! {
            interned_vec!($name, $ty, nofold);

            impl rustc_type_ir::fold::TypeFoldable<DbInterner> for $name {
                fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(self, folder: &mut F) -> Result<Self, F::Error> {
                    use rustc_type_ir::inherent::{SliceLike as _};
                    Ok($name(intern::Interned::new(InternedWrapper(self.iter().map(|v| v.try_fold_with(folder)).collect::<Result<_, _>>()?))))
                }
            }

            impl rustc_type_ir::visit::TypeVisitable<DbInterner> for $name {
                fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(&self, visitor: &mut V) -> V::Result {
                    use rustc_type_ir::inherent::{SliceLike as _};
                    use rustc_ast_ir::visit::VisitorResult;
                    rustc_ast_ir::walk_visitable_list!(visitor, self.as_slice().iter());
                    V::Result::output()
                }
            }
        }
    };
    ($name:ident, $ty:ty, nofold) => {
        paste::paste! {
            type [<Interned $name>] = intern::Interned<InternedWrapper<smallvec::SmallVec<[$ty; 2]>>>;

            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct $name([<Interned $name>]);

            impl $name {
                pub fn new_from_iter(data: impl IntoIterator<Item = $ty>) -> Self {
                    $name(intern::Interned::new(InternedWrapper(data.into_iter().collect())))
                }
            }

            impl rustc_type_ir::inherent::SliceLike for $name {
                type Item = $ty;

                type IntoIter = <smallvec::SmallVec<[$ty; 2]> as IntoIterator>::IntoIter;

                fn iter(self) -> Self::IntoIter {
                    self.0.0.clone().into_iter()
                }

                fn as_slice(&self) -> &[Self::Item] {
                    self.0.0.as_slice()
                }
            }

            impl IntoIterator for $name {
                type Item = $ty;
                type IntoIter = <Self as rustc_type_ir::inherent::SliceLike>::IntoIter;

                fn into_iter(self) -> Self::IntoIter { rustc_type_ir::inherent::SliceLike::iter(self) }
            }

            impl Default for $name {
                fn default() -> Self {
                    $name(intern::Interned::new(InternedWrapper(Default::default())))
                }
            }
        }
    };
}

pub use crate::_interned_vec as interned_vec;

#[derive(Debug, Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq)]
pub struct DbInterner;

impl inherent::DefId<DbInterner> for GenericDefId {
    fn as_local(self) -> Option<GenericDefId> {
        Some(self)
    }
    fn is_local(self) -> bool {
        true
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Span(Option<span::Span>);

impl inherent::Span<DbInterner> for Span {
    fn dummy() -> Self {
        Span(None)
    }
}

interned_vec!(BoundVarKinds, BoundVarKind, nofold);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum BoundVarKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

impl BoundVarKind {
    pub fn expect_region(self) -> BoundRegionKind {
        match self {
            BoundVarKind::Region(lt) => lt,
            _ => panic!("expected a region, but found another kind"),
        }
    }

    pub fn expect_ty(self) -> BoundTyKind {
        match self {
            BoundVarKind::Ty(ty) => ty,
            _ => panic!("expected a type, but found another kind"),
        }
    }

    pub fn expect_const(self) {
        match self {
            BoundVarKind::Const => (),
            _ => panic!("expected a const, but found another kind"),
        }
    }
}

interned_vec!(CanonicalVars, CanonicalVarInfo, nofold);

pub struct DepNodeIndex;

#[derive(Debug)]
pub struct Tracked<T: fmt::Debug + Clone>(T);

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)] // FIXME implement Debug by hand
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct AllocId;

impl rustc_type_ir::relate::Relate<DbInterner> for PatId {
    fn relate<R: rustc_type_ir::relate::TypeRelation>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        // FIXME implement this
        Ok(a)
    }
}

interned_vec!(VariancesOf, Variance, nofold);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct VariantIdx(usize);

// FIXME: could/should store actual data?
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum VariantDef {
    Struct(StructId),
    Union(UnionId),
    Enum(EnumVariantId),
}

impl VariantDef {
    pub fn id(&self) -> VariantId {
        match self {
            VariantDef::Struct(struct_id) => VariantId::StructId(*struct_id),
            VariantDef::Union(union_id) => VariantId::UnionId(*union_id),
            VariantDef::Enum(enum_variant_id) => VariantId::EnumVariantId(*enum_variant_id),
        }
    }

    pub fn fields(&self, db: &dyn HirDatabase) -> Vec<(Idx<FieldData>, FieldData)> {
        match self {
            VariantDef::Struct(it) => db
                .struct_data(*it)
                .variant_data
                .fields()
                .iter()
                .map(|(id, data)| (id, data.clone()))
                .collect(),
            VariantDef::Union(it) => db
                .union_data(*it)
                .variant_data
                .fields()
                .iter()
                .map(|(id, data)| (id, data.clone()))
                .collect(),
            VariantDef::Enum(it) => db
                .enum_variant_data(*it)
                .variant_data
                .fields()
                .iter()
                .map(|(id, data)| (id, data.clone()))
                .collect(),
        }
    }
}

/*
/// Definition of a variant -- a struct's fields or an enum variant.
#[derive(Debug, HashStable, TyEncodable, TyDecodable)]
pub struct VariantDef {
    /// `DefId` that identifies the variant itself.
    /// If this variant belongs to a struct or union, then this is a copy of its `DefId`.
    pub def_id: DefId,
    /// `DefId` that identifies the variant's constructor.
    /// If this variant is a struct variant, then this is `None`.
    pub ctor: Option<(CtorKind, DefId)>,
    /// Variant or struct name, maybe empty for anonymous adt (struct or union).
    pub name: Symbol,
    /// Discriminant of this variant.
    pub discr: VariantDiscr,
    /// Fields of this variant.
    pub fields: IndexVec<FieldIdx, FieldDef>,
    /// The error guarantees from parser, if any.
    tainted: Option<ErrorGuaranteed>,
    /// Flags of the variant (e.g. is field list non-exhaustive)?
    flags: VariantFlags,
}
*/

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct AdtFlags {
    is_enum: bool,
    is_union: bool,
    is_struct: bool,
    has_ctor: bool,
    is_phantom_data: bool,
    is_fundamental: bool,
    is_box: bool,
    is_manually_drop: bool,
    is_variant_list_non_exhaustive: bool,
    is_unsafe_cell: bool,
    is_anonymous: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDefData {
    pub id: AdtId,
    pub variants: Vec<(VariantIdx, VariantDef)>,
    pub flags: AdtFlags,
    pub repr: ReprOptions,
}

// We're gonna cheat a little bit and implement `Hash` on only the `DefId` and
// accept there might be collisions for def ids from different crates (or across
// different tests, oh my).
impl std::hash::Hash for AdtDefData {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, s: &mut H) {
        self.id.hash(s)
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct AdtDef(pub(crate) AdtDefData);

impl AdtDef {
    pub fn new(def_id: AdtId, db: &dyn HirDatabase) -> Self {
        let (flags, variants) = match def_id {
            AdtId::StructId(struct_id) => {
                let data = db.struct_data(struct_id);

                let flags = AdtFlags {
                    is_enum: false,
                    is_union: false,
                    is_struct: true,
                    has_ctor: false, // FIXME
                    is_phantom_data: data.flags.contains(StructFlags::IS_PHANTOM_DATA),
                    is_fundamental: data.flags.contains(StructFlags::IS_FUNDAMENTAL),
                    is_box: data.flags.contains(StructFlags::IS_BOX),
                    is_manually_drop: data.flags.contains(StructFlags::IS_MANUALLY_DROP),
                    is_unsafe_cell: data.flags.contains(StructFlags::IS_UNSAFE_CELL),
                    is_variant_list_non_exhaustive: false,
                    // FIXME: get this data
                    is_anonymous: false,
                };

                let variants = vec![(VariantIdx(0), VariantDef::Struct(struct_id))];

                (flags, variants)
            }
            AdtId::UnionId(union_id) => {
                let data = db.union_data(union_id);

                let flags = AdtFlags {
                    is_enum: false,
                    is_union: true,
                    is_struct: false,
                    has_ctor: false, // FIXME
                    is_phantom_data: false,
                    is_fundamental: false,
                    is_box: false,
                    is_manually_drop: false,
                    is_unsafe_cell: false,
                    is_variant_list_non_exhaustive: false,
                    // FIXME: get this data
                    is_anonymous: false,
                };

                let variants = vec![(VariantIdx(0), VariantDef::Union(union_id))];

                (flags, variants)
            }
            AdtId::EnumId(enum_id) => {
                let data = db.enum_data(enum_id);

                let flags = AdtFlags {
                    is_enum: true,
                    is_union: false,
                    is_struct: false,
                    has_ctor: false, // FIXME
                    is_phantom_data: false,
                    is_fundamental: false,
                    is_box: false,
                    is_manually_drop: false,
                    is_unsafe_cell: false,
                    // FIXME: get this data
                    is_variant_list_non_exhaustive: false,
                    is_anonymous: false,
                };

                let variants = data
                    .variants
                    .iter()
                    .enumerate()
                    .map(|(idx, v)| (VariantIdx(idx), v))
                    .map(|(idx, v)| (idx, VariantDef::Enum(v.0)))
                    .collect();

                (flags, variants)
            }
        };

        // FIXME: keep track of these
        let repr = ReprOptions {
            int: None,
            align: None,
            pack: None,
            flags: ReprFlags::empty(),
            field_shuffle_seed: Hash64::ZERO,
        };

        AdtDef(AdtDefData { id: def_id, variants, flags, repr })
    }

    pub fn is_enum(&self) -> bool {
        self.0.flags.is_enum
    }

    #[inline]
    pub fn repr(self) -> ReprOptions {
        self.0.repr
    }

    /// Asserts this is a struct or union and returns its unique variant.
    pub fn non_enum_variant(self) -> VariantDef {
        assert!(self.0.flags.is_struct || self.0.flags.is_union);
        self.0.variants[0].1.clone()
    }
}

impl inherent::AdtDef<DbInterner> for AdtDef {
    fn def_id(&self) -> <DbInterner as rustc_type_ir::Interner>::DefId {
        GenericDefId::AdtId(self.0.id)
    }

    fn is_struct(&self) -> bool {
        self.0.flags.is_struct
    }

    fn is_phantom_data(&self) -> bool {
        self.0.flags.is_phantom_data
    }

    fn is_fundamental(&self) -> bool {
        self.0.flags.is_fundamental
    }
}

impl<'cx> inherent::IrAdtDef<DbInterner, DbIr<'cx>> for AdtDef {
    fn struct_tail_ty(
        self,
        ir: DbIr<'cx>,
    ) -> Option<rustc_type_ir::EarlyBinder<DbInterner, <DbInterner as rustc_type_ir::Interner>::Ty>>
    {
        let db = ir.db;
        let hir_def::AdtId::StructId(struct_id) = self.0.id else {
            return None;
        };
        let id: VariantId = struct_id.into();
        let variant_data = &id.variant_data(db.upcast());
        let Some((last_idx, _)) = variant_data.fields().iter().last() else { return None };
        let field_types = field_types_query(ir.db, id);

        let last_ty = field_types[last_idx].clone();
        Some(last_ty)
    }

    fn all_field_tys(
        self,
        ir: DbIr<'cx>,
    ) -> rustc_type_ir::EarlyBinder<
        DbInterner,
        impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::Ty>,
    > {
        let db = ir.db;
        // FIXME: this is disabled just to match the behavior with chalk right now
        let field_tys = |id: VariantId| {
            let variant_data = id.variant_data(db.upcast());
            let fields = if variant_data.fields().is_empty() {
                vec![]
            } else {
                let field_types = field_types_query(ir.db, id);
                variant_data
                    .fields()
                    .iter()
                    .map(|(idx, _)| {
                        let ty = field_types[idx].clone();
                        ty.skip_binder()
                    })
                    .collect()
            };
        };
        let field_tys = |id: VariantId| vec![];
        let tys: Vec<_> = match self.0.id {
            hir_def::AdtId::StructId(id) => field_tys(id.into()),
            hir_def::AdtId::UnionId(id) => field_tys(id.into()),
            hir_def::AdtId::EnumId(id) => db
                .enum_data(id)
                .variants
                .iter()
                .flat_map(|&(variant_id, _)| field_tys(variant_id.into()))
                .collect(),
        };

        rustc_type_ir::EarlyBinder::bind(tys)
    }

    fn sized_constraint(
        self,
        ir: DbIr<'cx>,
    ) -> Option<rustc_type_ir::EarlyBinder<DbInterner, <DbInterner as rustc_type_ir::Interner>::Ty>>
    {
        if self.is_struct() {
            let tail_ty = self.all_field_tys(ir).skip_binder().into_iter().last()?;

            let constraint_ty = sized_constraint_for_ty(ir, tail_ty)?;

            Some(EarlyBinder::bind(constraint_ty))
        } else {
            None
        }
    }

    fn destructor(self, ir: DbIr<'cx>) -> Option<rustc_type_ir::solve::AdtDestructorKind> {
        todo!()
    }
}

impl fmt::Debug for AdtDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        crate::next_solver::tls::with_opt_db_out_of_thin_air(|db| match db {
            Some(db) => match self.0.id {
                AdtId::StructId(struct_id) => {
                    let data = db.struct_data(struct_id);
                    f.write_str(data.name.as_str())
                }
                AdtId::UnionId(union_id) => {
                    let data = db.union_data(union_id);
                    f.write_str(data.name.as_str())
                }
                AdtId::EnumId(enum_id) => {
                    let data = db.enum_data(enum_id);
                    f.write_str(data.name.as_str())
                }
            },
            None => f.write_str(&format!("AdtDef({:?})", self.0.id)),
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Features;

impl inherent::Features<DbInterner> for Features {
    fn generic_const_exprs(self) -> bool {
        false
    }

    fn coroutine_clone(self) -> bool {
        false
    }

    fn associated_const_equality(self) -> bool {
        false
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct UnsizingParams(pub(crate) BitSet<u32>);

impl std::ops::Deref for UnsizingParams {
    type Target = BitSet<u32>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl rustc_type_ir::Interner for DbInterner {
    type DefId = GenericDefId;
    type LocalDefId = GenericDefId;
    type Span = Span;

    type GenericArgs = GenericArgs;
    type GenericArgsSlice = GenericArgs;
    type GenericArg = GenericArg;

    type Term = Term;

    type BoundVarKinds = BoundVarKinds;
    type BoundVarKind = BoundVarKind;

    type PredefinedOpaques = PredefinedOpaques;

    fn mk_predefined_opaques_in_body(
        self,
        data: rustc_type_ir::solve::PredefinedOpaquesData<Self>,
    ) -> Self::PredefinedOpaques {
        PredefinedOpaques::new(data)
    }

    type DefiningOpaqueTypes = DefiningOpaqueTypes;

    type CanonicalVars = CanonicalVars;

    fn mk_canonical_var_infos(
        self,
        infos: &[rustc_type_ir::CanonicalVarInfo<Self>],
    ) -> Self::CanonicalVars {
        CanonicalVars::new_from_iter(infos.iter().cloned())
    }

    type ExternalConstraints = ExternalConstraints;

    fn mk_external_constraints(
        self,
        data: rustc_type_ir::solve::ExternalConstraintsData<Self>,
    ) -> Self::ExternalConstraints {
        ExternalConstraints::new(data)
    }

    type DepNodeIndex = DepNodeIndex;

    type Tracked<T: fmt::Debug + Clone> = Tracked<T>;

    type Ty = Ty;
    type Tys = Tys;
    type FnInputTys = Tys;
    type ParamTy = ParamTy;
    type BoundTy = BoundTy;
    type PlaceholderTy = PlaceholderTy;

    type ErrorGuaranteed = ErrorGuaranteed;
    type BoundExistentialPredicates = BoundExistentialPredicates;
    type AllocId = AllocId;
    type Pat = PatId;
    type Safety = Safety;
    type Abi = FnAbi;

    type Const = Const;
    type PlaceholderConst = PlaceholderConst;
    type ParamConst = ParamConst;
    type BoundConst = rustc_type_ir::BoundVar;
    type ValueConst = ValueConst;
    type ExprConst = ExprConst;

    type Region = Region;
    type EarlyParamRegion = EarlyParamRegion;
    type LateParamRegion = LateParamRegion;
    type BoundRegion = BoundRegion;
    type PlaceholderRegion = PlaceholderRegion;

    type ParamEnv = ParamEnv;
    type Predicate = Predicate;
    type Clause = Clause;
    type Clauses = Clauses;

    type GenericsOf = Generics;

    type VariancesOf = VariancesOf;

    type AdtDef = AdtDef;

    type Features = Features;

    fn mk_args(self, args: &[Self::GenericArg]) -> Self::GenericArgs {
        GenericArgs::new_from_iter(args.iter().cloned())
    }

    fn mk_args_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self::GenericArg, Self::GenericArgs>,
    {
        CollectAndApply::collect_and_apply(args, |g| GenericArgs::new_from_iter(g.iter().cloned()))
    }

    type UnsizingParams = UnsizingParams;
}

impl DbInterner {
    pub fn shift_bound_var_indices<T>(self, bound_vars: usize, value: T) -> T
    where
        T: rustc_type_ir::fold::TypeFoldable<Self>,
    {
        let shift_bv = |bv: BoundVar| BoundVar::from_usize(bv.as_usize() + bound_vars);
        self.replace_escaping_bound_vars_uncached(
            value,
            FnMutDelegate {
                regions: &mut |r: BoundRegion| {
                    Region::new_bound(
                        self,
                        DebruijnIndex::ZERO,
                        BoundRegion { var: shift_bv(r.var), kind: r.kind },
                    )
                },
                types: &mut |t: BoundTy| {
                    Ty::new_bound(
                        self,
                        DebruijnIndex::ZERO,
                        BoundTy { var: shift_bv(t.var), kind: t.kind },
                    )
                },
                consts: &mut |c| Const::new_bound(self, DebruijnIndex::ZERO, shift_bv(c)),
            },
        )
    }

    pub fn replace_escaping_bound_vars_uncached<
        T: rustc_type_ir::fold::TypeFoldable<DbInterner>,
    >(
        self,
        value: T,
        delegate: impl BoundVarReplacerDelegate,
    ) -> T {
        if !value.has_escaping_bound_vars() {
            value
        } else {
            let mut replacer = BoundVarReplacer::new(self, delegate);
            value.fold_with(&mut replacer)
        }
    }

    pub fn replace_bound_vars_uncached<T: rustc_type_ir::fold::TypeFoldable<DbInterner>>(
        self,
        value: Binder<T>,
        delegate: impl BoundVarReplacerDelegate,
    ) -> T {
        self.replace_escaping_bound_vars_uncached(value.skip_binder(), delegate)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct DbIr<'a> {
    pub(crate) db: &'a dyn HirDatabase,
    pub(crate) krate: CrateId,
    pub(crate) block: Option<BlockId>,
}

impl<'a> DbIr<'a> {
    pub fn new(db: &'a dyn HirDatabase, krate: CrateId, block: Option<BlockId>) -> Self {
        DbIr { db, krate, block }
    }
}
impl RustIr for DbIr<'_> {
    type Interner = DbInterner;

    fn interner(self) -> Self::Interner {
        DbInterner
    }

    fn mk_tracked<T: fmt::Debug + Clone>(
        self,
        data: T,
        dep_node: <Self::Interner as rustc_type_ir::Interner>::DepNodeIndex,
    ) -> <Self::Interner as rustc_type_ir::Interner>::Tracked<T> {
        Tracked(data)
    }

    fn get_tracked<T: fmt::Debug + Clone>(
        self,
        tracked: &<Self::Interner as rustc_type_ir::Interner>::Tracked<T>,
    ) -> T {
        tracked.0.clone()
    }

    fn with_cached_task<T>(
        self,
        task: impl FnOnce() -> T,
    ) -> (T, <Self::Interner as rustc_type_ir::Interner>::DepNodeIndex) {
        (task(), DepNodeIndex)
    }

    fn with_global_cache<R>(
        self,
        f: impl FnOnce(&mut rustc_type_ir::search_graph::GlobalCache<Self>) -> R,
    ) -> R {
        let mut cache = rustc_type_ir::search_graph::GlobalCache::default();
        f(&mut cache)
    }

    fn evaluation_is_concurrent(&self) -> bool {
        false
    }

    fn expand_abstract_consts<T: rustc_type_ir::fold::TypeFoldable<Self::Interner>>(
        self,
        t: T,
    ) -> T {
        t
    }

    fn generics_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::GenericsOf {
        generics(self.db.upcast(), def_id)
    }

    fn variances_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::VariancesOf {
        match def_id {
            GenericDefId::FunctionId(def_id) => {
                HirDatabase::fn_def_variance(self.db, chalk_ir::FnDefId(def_id.as_intern_id()))
                    .to_nextsolver(self)
            }
            GenericDefId::AdtId(def_id) => {
                HirDatabase::adt_variance(self.db, chalk_ir::AdtId(def_id)).to_nextsolver(self)
            }
            GenericDefId::OpaqueTyId(_def_id) => {
                // FIXME: track variances
                VariancesOf::new_from_iter(
                    (0..self.generics_of(def_id).count()).map(|_| Variance::Invariant),
                )
            }
            _ => todo!(),
        }
    }

    fn type_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self::Interner, <Self::Interner as rustc_type_ir::Interner>::Ty>
    {
        let def_id = match def_id {
            GenericDefId::TypeAliasId(id) => {
                use hir_def::Lookup;
                match id.lookup(self.db.upcast()).container {
                    ItemContainerId::ImplId(it) => it,
                    _ => panic!("assoc ty value should be in impl"),
                };
                crate::TyDefId::TypeAliasId(id)
            }
            _ => todo!(),
        };
        ty_query(self.db, def_id)
    }

    fn adt_def(
        self,
        adt_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::AdtDef {
        let def_id = match adt_def_id {
            GenericDefId::AdtId(adt_id) => adt_id,
            _ => panic!("Invalid DefId passed to adt_def"),
        };
        AdtDef::new(def_id, self.db)
    }

    fn alias_ty_kind(
        self,
        alias: rustc_type_ir::AliasTy<Self::Interner>,
    ) -> rustc_type_ir::AliasTyKind {
        // FIXME: not currently creating any others
        rustc_type_ir::AliasTyKind::Projection
    }

    fn alias_term_kind(
        self,
        alias: rustc_type_ir::AliasTerm<Self::Interner>,
    ) -> rustc_type_ir::AliasTermKind {
        match alias.def_id {
            GenericDefId::OpaqueTyId(_) => AliasTermKind::OpaqueTy,
            GenericDefId::TypeAliasId(_) => AliasTermKind::ProjectionTy,
            _ => todo!(),
        }
    }

    fn trait_ref_and_own_args_for_alias(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        args: <Self::Interner as rustc_type_ir::Interner>::GenericArgs,
    ) -> (
        rustc_type_ir::TraitRef<Self::Interner>,
        <Self::Interner as rustc_type_ir::Interner>::GenericArgsSlice,
    ) {
        let trait_def_id = self.parent(def_id);
        let generics = self.generics_of(def_id);
        let alias_args =
            GenericArgs::new_from_iter(args.clone().iter().take(generics.own_params.len()));
        let trait_args = GenericArgs::new_from_iter(
            args.as_slice()[generics.own_params.len()..].iter().cloned(),
        );
        (TraitRef::new_from_args(self, trait_def_id, trait_args), alias_args)
    }

    fn check_args_compatible(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        args: <Self::Interner as rustc_type_ir::Interner>::GenericArgs,
    ) -> bool {
        // FIXME
        true
    }

    fn debug_assert_args_compatible(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        args: <Self::Interner as rustc_type_ir::Interner>::GenericArgs,
    ) {
    }

    fn debug_assert_existential_args_compatible(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        args: <Self::Interner as rustc_type_ir::Interner>::GenericArgs,
    ) {
    }

    fn mk_type_list_from_iter<I, T>(self, args: I) -> T::Output
    where
        I: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<
            <Self::Interner as rustc_type_ir::Interner>::Ty,
            <Self::Interner as rustc_type_ir::Interner>::Tys,
        >,
    {
        CollectAndApply::collect_and_apply(args, |g| Tys::new_from_iter(g.iter().cloned()))
    }

    fn parent(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::DefId {
        use hir_def::Lookup;

        let container = match def_id {
            GenericDefId::FunctionId(it) => it.lookup(self.db.upcast()).container,
            GenericDefId::TypeAliasId(it) => it.lookup(self.db.upcast()).container,
            GenericDefId::ConstId(it) => it.lookup(self.db.upcast()).container,
            GenericDefId::ClosureId(it) => {
                return it
                    .lookup(self.db.upcast())
                    .parent
                    .as_generic_def_id(self.db.upcast())
                    .unwrap()
            }
            GenericDefId::CoroutineId(it) => {
                return it
                    .lookup(self.db.upcast())
                    .parent
                    .as_generic_def_id(self.db.upcast())
                    .unwrap()
            }
            GenericDefId::OpaqueTyId(it) => todo!(),
            GenericDefId::StaticId(_)
            | GenericDefId::AdtId(_)
            | GenericDefId::TraitId(_)
            | GenericDefId::ImplId(_)
            | GenericDefId::TraitAliasId(_)
            | GenericDefId::Ctor(..) => panic!(),
        };

        match container {
            ItemContainerId::ImplId(it) => it.into(),
            ItemContainerId::TraitId(it) => it.into(),
            ItemContainerId::ModuleId(_) | ItemContainerId::ExternBlockId(_) => panic!(),
        }
    }

    fn recursion_limit(self) -> usize {
        50
    }

    fn features(self) -> <Self::Interner as rustc_type_ir::Interner>::Features {
        Features
    }

    fn bound_coroutine_hidden_types(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> impl IntoIterator<
        Item = rustc_type_ir::EarlyBinder<
            Self::Interner,
            rustc_type_ir::Binder<Self::Interner, <Self::Interner as rustc_type_ir::Interner>::Ty>,
        >,
    > {
        [todo!()]
    }

    fn fn_sig(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        rustc_type_ir::Binder<Self::Interner, rustc_type_ir::FnSig<Self::Interner>>,
    > {
        let id = match def_id {
            GenericDefId::FunctionId(id) => CallableDefId::FunctionId(id),
            GenericDefId::AdtId(id) => match id {
                AdtId::StructId(id) => CallableDefId::StructId(id),
                _ => todo!(),
            },
            _ => unreachable!(),
        };
        callable_item_sig(self.db, id)
    }

    fn coroutine_movability(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_ast_ir::Movability {
        todo!()
    }

    fn coroutine_for_closure(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::DefId {
        todo!()
    }

    fn generics_require_sized_self(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        let sized_trait = self.db.lang_item(self.krate, LangItem::Sized);
        let Some(sized_id) = sized_trait.and_then(|t| t.as_trait()) else {
            return false; /* No Sized trait, can't require it! */
        };
        let sized_def_id = sized_id.into();

        // Search for a predicate like `Self : Sized` amongst the trait bounds.
        let predicates = self.predicates_of(def_id);
        // FIXME: I don't think this worked for generic associated associated types,
        // because the parent args are *after* the item args
        elaborate(self, predicates.iter_identity()).any(|pred| match pred.kind().skip_binder() {
            ClauseKind::Trait(ref trait_pred) => {
                trait_pred.def_id() == sized_def_id
                    && matches!(
                        trait_pred.self_ty().clone().kind(),
                        TyKind::Param(ParamTy { index: 0, .. })
                    )
            }
            ClauseKind::RegionOutlives(_)
            | ClauseKind::TypeOutlives(_)
            | ClauseKind::Projection(_)
            | ClauseKind::ConstArgHasType(_, _)
            | ClauseKind::WellFormed(_)
            | ClauseKind::ConstEvaluatable(_)
            | ClauseKind::HostEffect(..) => false,
        })
    }

    fn item_bounds(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<Item = <Self::Interner as rustc_type_ir::Interner>::Clause>,
    > {
        match def_id {
            GenericDefId::TypeAliasId(type_alias) => {
                let trait_ = match type_alias.lookup(self.db.upcast()).container {
                    ItemContainerId::TraitId(t) => t,
                    _ => panic!("associated type not in trait"),
                };

                let db = self.db;
                // Lower bounds -- we could/should maybe move this to a separate query in `lower`
                let type_alias_data = db.type_alias_data(type_alias);
                let generic_params = generics(db.upcast(), type_alias.into());
                let resolver = hir_def::resolver::HasResolver::resolver(type_alias, db.upcast());
                let mut ctx = TyLoweringContext::new(
                    db,
                    &resolver,
                    &type_alias_data.types_map,
                    type_alias.into(),
                );

                let trait_args = GenericArgs::identity_for_item(self, trait_.into());
                let item_args = GenericArgs::identity_for_item(self, def_id);
                let self_ty = Ty::new_projection_from_args(self, def_id, item_args);

                let mut bounds = Vec::new();
                for bound in &type_alias_data.bounds {
                    ctx.lower_type_bound(bound, self_ty.clone(), false).for_each(|pred| {
                        bounds.push(pred);
                    });
                }

                if !ctx.unsized_types.contains(&self_ty) {
                    let sized_trait = ctx.db.lang_item(self.krate, LangItem::Sized);
                    let sized_bound = sized_trait.map(|trait_id| {
                        let trait_ref = TraitRef::new_from_args(
                            self,
                            trait_id.as_trait().unwrap().into(),
                            GenericArgs::new_from_iter([self_ty.clone().into()]),
                        );
                        Clause(Predicate::new(Binder::dummy(rustc_type_ir::PredicateKind::Clause(
                            rustc_type_ir::ClauseKind::Trait(TraitPredicate {
                                trait_ref,
                                polarity: rustc_type_ir::PredicatePolarity::Positive,
                            }),
                        ))))
                    });
                    bounds.extend(sized_bound);
                    bounds.shrink_to_fit();
                }

                rustc_type_ir::EarlyBinder::bind(bounds)
            }
            GenericDefId::OpaqueTyId(id) => {
                let full_id = self.db.lookup_intern_opaque_ty(id);
                match full_id {
                    OpaqueTyLoc::ReturnTypeImplTrait(func, idx) => {
                        let datas = return_type_impl_traits(self.db, func)
                            .expect("impl trait id without impl traits");
                        let datas = (*datas).as_ref().skip_binder();
                        let data = &datas.impl_traits[Idx::from_raw(idx)];
                        let predicates: Vec<Clause> =
                            elaborate(self, data.predicates.clone()).collect();
                        EarlyBinder::bind(predicates)
                    }
                    OpaqueTyLoc::TypeAliasImplTrait(alias, idx) => {
                        let datas = type_alias_impl_traits(self.db, alias)
                            .expect("impl trait id without impl traits");
                        let datas = (*datas).as_ref().skip_binder();
                        let data = &datas.impl_traits[Idx::from_raw(idx)];
                        let predicates: Vec<Clause> =
                            elaborate(self, data.predicates.clone()).collect();
                        EarlyBinder::bind(predicates)
                    }
                    OpaqueTyLoc::AsyncBlockTypeImplTrait(..) => {
                        if let Some((future_trait, future_output)) = self
                            .db
                            .lang_item(self.krate, LangItem::Future)
                            .and_then(|item| item.as_trait())
                            .and_then(|trait_| {
                                let alias = self.db.trait_data(trait_).associated_type_by_name(
                                    &hir_expand::name::Name::new_symbol_root(sym::Output.clone()),
                                )?;
                                Some((trait_, alias))
                            })
                        {
                            let args = GenericArgs::identity_for_item(self, def_id);
                            let mut predicates = vec![];

                            let item_ty = Ty::new_alias(
                                DbInterner,
                                rustc_type_ir::AliasTyKind::Opaque,
                                AliasTy::new_from_args(self, def_id, args),
                            );

                            let kind = PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                                polarity: rustc_type_ir::PredicatePolarity::Positive,
                                trait_ref: TraitRef::new_from_args(
                                    self,
                                    future_trait.into(),
                                    GenericArgs::new_from_iter([item_ty.clone().into()]),
                                ),
                            }));
                            predicates.push(Clause(Predicate::new(Binder::bind_with_vars(
                                kind,
                                BoundVarKinds::new_from_iter([BoundVarKind::Ty(BoundTyKind::Anon)]),
                            ))));
                            let sized_trait = self
                                .db
                                .lang_item(self.krate, LangItem::Sized)
                                .and_then(|item| item.as_trait());
                            if let Some(sized_trait_) = sized_trait {
                                let kind =
                                    PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                                        polarity: rustc_type_ir::PredicatePolarity::Positive,
                                        trait_ref: TraitRef::new_from_args(
                                            self,
                                            sized_trait_.into(),
                                            GenericArgs::new_from_iter([item_ty.clone().into()]),
                                        ),
                                    }));
                                predicates.push(Clause(Predicate::new(Binder::bind_with_vars(
                                    kind,
                                    BoundVarKinds::new_from_iter([BoundVarKind::Ty(
                                        BoundTyKind::Anon,
                                    )]),
                                ))));
                            }
                            EarlyBinder::bind(predicates)
                        } else {
                            // If failed to find Symbol’s value as variable is void: Future::Output, return empty bounds as fallback.
                            EarlyBinder::bind(vec![])
                        }
                    }
                }
            }
            _ => panic!("Unexpected GeneridDefId"),
        }
    }

    #[tracing::instrument(level = "debug", skip(self), ret)]
    fn predicates_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<Item = <Self::Interner as rustc_type_ir::Interner>::Clause>,
    > {
        let predicates = generic_predicates_query(self.db, def_id);
        let predicates: Vec<_> = predicates.iter().cloned().collect();
        EarlyBinder::bind(predicates.into_iter())
    }

    #[tracing::instrument(level = "debug", skip(self), ret)]
    fn own_predicates_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<Item = <Self::Interner as rustc_type_ir::Interner>::Clause>,
    > {
        let predicates = generic_predicates_without_parent_query(self.db, def_id);
        let predicates: Vec<_> = predicates.iter().cloned().collect();
        EarlyBinder::bind(predicates.into_iter())
    }

    fn explicit_super_predicates_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<
            Item = (
                <Self::Interner as rustc_type_ir::Interner>::Clause,
                <Self::Interner as rustc_type_ir::Interner>::Span,
            ),
        >,
    > {
        let predicates: Vec<(Clause, Span)> =
            lower_nextsolver::generic_predicates_filtered_by(self.db, def_id, |def_id| true)
                .iter()
                .cloned()
                .map(|p| (p, Span::dummy()))
                .collect();
        rustc_type_ir::EarlyBinder::bind(predicates)
    }

    fn explicit_implied_predicates_of(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<
            Item = (
                <Self::Interner as rustc_type_ir::Interner>::Clause,
                <Self::Interner as rustc_type_ir::Interner>::Span,
            ),
        >,
    > {
        let predicates: Vec<(Clause, Span)> =
            lower_nextsolver::generic_predicates_filtered_by(self.db, def_id, |def_id| true)
                .iter()
                .cloned()
                .map(|p| (p, Span::dummy()))
                .collect();
        rustc_type_ir::EarlyBinder::bind(predicates)
    }

    fn const_conditions(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<
            Item = rustc_type_ir::Binder<Self::Interner, rustc_type_ir::TraitRef<Self::Interner>>,
        >,
    > {
        rustc_type_ir::EarlyBinder::bind([todo!()])
    }

    fn has_target_features(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        false
    }

    fn require_lang_item(
        self,
        lang_item: rustc_type_ir::lang_items::TraitSolverLangItem,
    ) -> <Self::Interner as rustc_type_ir::Interner>::DefId {
        let lang_item = match lang_item {
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncDestruct => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFn => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnKindHelper => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnKindUpvars => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnMut => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnOnce => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnOnceOutput => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::AsyncIterator => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::CallOnceFuture => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::CallRefFuture => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::Clone => LangItem::Clone,
            rustc_type_ir::lang_items::TraitSolverLangItem::Copy => LangItem::Copy,
            rustc_type_ir::lang_items::TraitSolverLangItem::Coroutine => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::CoroutineReturn => LangItem::Coroutine,
            rustc_type_ir::lang_items::TraitSolverLangItem::CoroutineYield => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::Destruct => LangItem::Destruct,
            rustc_type_ir::lang_items::TraitSolverLangItem::DiscriminantKind => {
                LangItem::DiscriminantKind
            }
            rustc_type_ir::lang_items::TraitSolverLangItem::Drop => LangItem::Drop,
            rustc_type_ir::lang_items::TraitSolverLangItem::DynMetadata => LangItem::DynMetadata,
            rustc_type_ir::lang_items::TraitSolverLangItem::Fn => LangItem::Fn,
            rustc_type_ir::lang_items::TraitSolverLangItem::FnMut => LangItem::FnMut,
            rustc_type_ir::lang_items::TraitSolverLangItem::FnOnce => LangItem::FnOnce,
            rustc_type_ir::lang_items::TraitSolverLangItem::FnPtrTrait => LangItem::FnPtrTrait,
            rustc_type_ir::lang_items::TraitSolverLangItem::FusedIterator => todo!(),
            rustc_type_ir::lang_items::TraitSolverLangItem::Future => LangItem::Future,
            rustc_type_ir::lang_items::TraitSolverLangItem::FutureOutput => LangItem::FutureOutput,
            rustc_type_ir::lang_items::TraitSolverLangItem::Iterator => LangItem::Iterator,
            rustc_type_ir::lang_items::TraitSolverLangItem::Metadata => LangItem::Metadata,
            rustc_type_ir::lang_items::TraitSolverLangItem::Option => LangItem::Option,
            rustc_type_ir::lang_items::TraitSolverLangItem::PointeeTrait => LangItem::PointeeTrait,
            rustc_type_ir::lang_items::TraitSolverLangItem::Poll => LangItem::Poll,
            rustc_type_ir::lang_items::TraitSolverLangItem::Sized => LangItem::Sized,
            rustc_type_ir::lang_items::TraitSolverLangItem::TransmuteTrait => {
                LangItem::TransmuteTrait
            }
            rustc_type_ir::lang_items::TraitSolverLangItem::Tuple => LangItem::Tuple,
            rustc_type_ir::lang_items::TraitSolverLangItem::Unpin => LangItem::Unpin,
            rustc_type_ir::lang_items::TraitSolverLangItem::Unsize => LangItem::Unsize,
        };
        let target = self
            .db
            .lang_item(self.krate, lang_item)
            .unwrap_or_else(|| panic!("Lang item {lang_item:?} required but not found."));
        match target {
            hir_def::lang_item::LangItemTarget::EnumId(enum_id) => enum_id.into(),
            hir_def::lang_item::LangItemTarget::Function(function_id) => function_id.into(),
            hir_def::lang_item::LangItemTarget::ImplDef(impl_id) => impl_id.into(),
            hir_def::lang_item::LangItemTarget::Static(static_id) => todo!(),
            hir_def::lang_item::LangItemTarget::Struct(struct_id) => struct_id.into(),
            hir_def::lang_item::LangItemTarget::Union(union_id) => union_id.into(),
            hir_def::lang_item::LangItemTarget::TypeAlias(type_alias_id) => type_alias_id.into(),
            hir_def::lang_item::LangItemTarget::Trait(trait_id) => trait_id.into(),
            hir_def::lang_item::LangItemTarget::EnumVariant(enum_variant_id) => todo!(),
        }
    }

    fn is_lang_item(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        lang_item: rustc_type_ir::lang_items::TraitSolverLangItem,
    ) -> bool {
        use rustc_type_ir::lang_items::TraitSolverLangItem::*;

        // FIXME: derive PartialEq on TraitSolverLangItem
        self.as_lang_item(def_id).map_or(false, |l| match (l, lang_item) {
            (AsyncDestruct, AsyncDestruct) => true,
            (AsyncFn, AsyncFn) => true,
            (AsyncFnKindHelper, AsyncFnKindHelper) => true,
            (AsyncFnKindUpvars, AsyncFnKindUpvars) => true,
            (AsyncFnMut, AsyncFnMut) => true,
            (AsyncFnOnce, AsyncFnOnce) => true,
            (AsyncFnOnceOutput, AsyncFnOnceOutput) => true,
            (AsyncIterator, AsyncIterator) => true,
            (CallOnceFuture, CallOnceFuture) => true,
            (CallRefFuture, CallRefFuture) => true,
            (Clone, Clone) => true,
            (Copy, Copy) => true,
            (Coroutine, Coroutine) => true,
            (CoroutineReturn, CoroutineReturn) => true,
            (CoroutineYield, CoroutineYield) => true,
            (Destruct, Destruct) => true,
            (DiscriminantKind, DiscriminantKind) => true,
            (Drop, Drop) => true,
            (DynMetadata, DynMetadata) => true,
            (Fn, Fn) => true,
            (FnMut, FnMut) => true,
            (FnOnce, FnOnce) => true,
            (FnPtrTrait, FnPtrTrait) => true,
            (FusedIterator, FusedIterator) => true,
            (Future, Future) => true,
            (FutureOutput, FutureOutput) => true,
            (Iterator, Iterator) => true,
            (Metadata, Metadata) => true,
            (Option, Option) => true,
            (PointeeTrait, PointeeTrait) => true,
            (Poll, Poll) => true,
            (Sized, Sized) => true,
            (TransmuteTrait, TransmuteTrait) => true,
            (Tuple, Tuple) => true,
            (Unpin, Unpin) => true,
            (Unsize, Unsize) => true,
            _ => false,
        })
    }

    fn as_lang_item(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> Option<rustc_type_ir::lang_items::TraitSolverLangItem> {
        let trait_ = match def_id {
            GenericDefId::TraitId(id) => id,
            _ => panic!("Unexpected GenericDefId in as_lang_item"),
        };
        let lang_item = self.db.lang_attr(trait_.into())?;
        Some(match lang_item {
            hir_def::lang_item::LangItem::Sized => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Sized
            }
            hir_def::lang_item::LangItem::Unsize => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Unsize
            }
            hir_def::lang_item::LangItem::StructuralPeq => return None,
            hir_def::lang_item::LangItem::StructuralTeq => return None,
            hir_def::lang_item::LangItem::Copy => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Copy
            }
            hir_def::lang_item::LangItem::Clone => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Clone
            }
            hir_def::lang_item::LangItem::Sync => return None,
            hir_def::lang_item::LangItem::DiscriminantKind => {
                rustc_type_ir::lang_items::TraitSolverLangItem::DiscriminantKind
            }
            hir_def::lang_item::LangItem::Discriminant => return None,
            hir_def::lang_item::LangItem::PointeeTrait => {
                rustc_type_ir::lang_items::TraitSolverLangItem::PointeeTrait
            }
            hir_def::lang_item::LangItem::Metadata => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Metadata
            }
            hir_def::lang_item::LangItem::DynMetadata => {
                rustc_type_ir::lang_items::TraitSolverLangItem::DynMetadata
            }
            hir_def::lang_item::LangItem::Freeze => return None,
            hir_def::lang_item::LangItem::FnPtrTrait => {
                rustc_type_ir::lang_items::TraitSolverLangItem::FnPtrTrait
            }
            hir_def::lang_item::LangItem::FnPtrAddr => return None,
            hir_def::lang_item::LangItem::Drop => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Drop
            }
            hir_def::lang_item::LangItem::Destruct => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Destruct
            }
            hir_def::lang_item::LangItem::CoerceUnsized => return None,
            hir_def::lang_item::LangItem::DispatchFromDyn => return None,
            hir_def::lang_item::LangItem::TransmuteOpts => return None,
            hir_def::lang_item::LangItem::TransmuteTrait => {
                rustc_type_ir::lang_items::TraitSolverLangItem::TransmuteTrait
            }
            hir_def::lang_item::LangItem::Add => return None,
            hir_def::lang_item::LangItem::Sub => return None,
            hir_def::lang_item::LangItem::Mul => return None,
            hir_def::lang_item::LangItem::Div => return None,
            hir_def::lang_item::LangItem::Rem => return None,
            hir_def::lang_item::LangItem::Neg => return None,
            hir_def::lang_item::LangItem::Not => return None,
            hir_def::lang_item::LangItem::BitXor => return None,
            hir_def::lang_item::LangItem::BitAnd => return None,
            hir_def::lang_item::LangItem::BitOr => return None,
            hir_def::lang_item::LangItem::Shl => return None,
            hir_def::lang_item::LangItem::Shr => return None,
            hir_def::lang_item::LangItem::AddAssign => return None,
            hir_def::lang_item::LangItem::SubAssign => return None,
            hir_def::lang_item::LangItem::MulAssign => return None,
            hir_def::lang_item::LangItem::DivAssign => return None,
            hir_def::lang_item::LangItem::RemAssign => return None,
            hir_def::lang_item::LangItem::BitXorAssign => return None,
            hir_def::lang_item::LangItem::BitAndAssign => return None,
            hir_def::lang_item::LangItem::BitOrAssign => return None,
            hir_def::lang_item::LangItem::ShlAssign => return None,
            hir_def::lang_item::LangItem::ShrAssign => return None,
            hir_def::lang_item::LangItem::Index => return None,
            hir_def::lang_item::LangItem::IndexMut => return None,
            hir_def::lang_item::LangItem::UnsafeCell => return None,
            hir_def::lang_item::LangItem::VaList => return None,
            hir_def::lang_item::LangItem::Deref => return None,
            hir_def::lang_item::LangItem::DerefMut => return None,
            hir_def::lang_item::LangItem::DerefTarget => return None,
            hir_def::lang_item::LangItem::Receiver => return None,
            hir_def::lang_item::LangItem::ReceiverTarget => return None,
            hir_def::lang_item::LangItem::Ordering => return None,
            hir_def::lang_item::LangItem::PanicNullPointerDereference => return None,
            hir_def::lang_item::LangItem::Fn => rustc_type_ir::lang_items::TraitSolverLangItem::Fn,
            hir_def::lang_item::LangItem::FnMut => {
                rustc_type_ir::lang_items::TraitSolverLangItem::FnMut
            }
            hir_def::lang_item::LangItem::FnOnce => {
                rustc_type_ir::lang_items::TraitSolverLangItem::FnOnce
            }
            hir_def::lang_item::LangItem::FnOnceOutput => return None,
            hir_def::lang_item::LangItem::AsyncFn => {
                rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFn
            }
            hir_def::lang_item::LangItem::AsyncFnMut => {
                rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnMut
            }
            hir_def::lang_item::LangItem::AsyncFnOnce => {
                rustc_type_ir::lang_items::TraitSolverLangItem::AsyncFnOnce
            }
            hir_def::lang_item::LangItem::Future => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Future
            }
            hir_def::lang_item::LangItem::CoroutineState => return None,
            hir_def::lang_item::LangItem::Coroutine => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Coroutine
            }
            hir_def::lang_item::LangItem::Unpin => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Unpin
            }
            hir_def::lang_item::LangItem::Pin => return None,
            hir_def::lang_item::LangItem::PartialEq => return None,
            hir_def::lang_item::LangItem::PartialOrd => return None,
            hir_def::lang_item::LangItem::CVoid => return None,
            hir_def::lang_item::LangItem::Panic => return None,
            hir_def::lang_item::LangItem::PanicNounwind => return None,
            hir_def::lang_item::LangItem::PanicFmt => return None,
            hir_def::lang_item::LangItem::PanicDisplay => return None,
            hir_def::lang_item::LangItem::ConstPanicFmt => return None,
            hir_def::lang_item::LangItem::PanicBoundsCheck => return None,
            hir_def::lang_item::LangItem::PanicMisalignedPointerDereference => return None,
            hir_def::lang_item::LangItem::PanicInfo => return None,
            hir_def::lang_item::LangItem::PanicLocation => return None,
            hir_def::lang_item::LangItem::PanicImpl => return None,
            hir_def::lang_item::LangItem::PanicCannotUnwind => return None,
            hir_def::lang_item::LangItem::BeginPanic => return None,
            hir_def::lang_item::LangItem::FormatAlignment => return None,
            hir_def::lang_item::LangItem::FormatArgument => return None,
            hir_def::lang_item::LangItem::FormatArguments => return None,
            hir_def::lang_item::LangItem::FormatCount => return None,
            hir_def::lang_item::LangItem::FormatPlaceholder => return None,
            hir_def::lang_item::LangItem::FormatUnsafeArg => return None,
            hir_def::lang_item::LangItem::ExchangeMalloc => return None,
            hir_def::lang_item::LangItem::BoxFree => return None,
            hir_def::lang_item::LangItem::DropInPlace => return None,
            hir_def::lang_item::LangItem::AllocLayout => return None,
            hir_def::lang_item::LangItem::Start => return None,
            hir_def::lang_item::LangItem::EhPersonality => return None,
            hir_def::lang_item::LangItem::EhCatchTypeinfo => return None,
            hir_def::lang_item::LangItem::OwnedBox => return None,
            hir_def::lang_item::LangItem::PhantomData => return None,
            hir_def::lang_item::LangItem::ManuallyDrop => return None,
            hir_def::lang_item::LangItem::MaybeUninit => return None,
            hir_def::lang_item::LangItem::AlignOffset => return None,
            hir_def::lang_item::LangItem::Termination => return None,
            hir_def::lang_item::LangItem::Try => return None,
            hir_def::lang_item::LangItem::Tuple => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Tuple
            }
            hir_def::lang_item::LangItem::SliceLen => return None,
            hir_def::lang_item::LangItem::TryTraitFromResidual => return None,
            hir_def::lang_item::LangItem::TryTraitFromOutput => return None,
            hir_def::lang_item::LangItem::TryTraitBranch => return None,
            hir_def::lang_item::LangItem::TryTraitFromYeet => return None,
            hir_def::lang_item::LangItem::PointerLike => return None,
            hir_def::lang_item::LangItem::ConstParamTy => return None,
            hir_def::lang_item::LangItem::Poll => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Poll
            }
            hir_def::lang_item::LangItem::PollReady => return None,
            hir_def::lang_item::LangItem::PollPending => return None,
            hir_def::lang_item::LangItem::ResumeTy => return None,
            hir_def::lang_item::LangItem::GetContext => return None,
            hir_def::lang_item::LangItem::Context => return None,
            hir_def::lang_item::LangItem::FuturePoll => return None,
            hir_def::lang_item::LangItem::FutureOutput => {
                rustc_type_ir::lang_items::TraitSolverLangItem::FutureOutput
            }
            hir_def::lang_item::LangItem::Option => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Option
            }
            hir_def::lang_item::LangItem::OptionSome => return None,
            hir_def::lang_item::LangItem::OptionNone => return None,
            hir_def::lang_item::LangItem::ResultOk => return None,
            hir_def::lang_item::LangItem::ResultErr => return None,
            hir_def::lang_item::LangItem::ControlFlowContinue => return None,
            hir_def::lang_item::LangItem::ControlFlowBreak => return None,
            hir_def::lang_item::LangItem::IntoFutureIntoFuture => return None,
            hir_def::lang_item::LangItem::IntoIterIntoIter => return None,
            hir_def::lang_item::LangItem::IteratorNext => return None,
            hir_def::lang_item::LangItem::Iterator => {
                rustc_type_ir::lang_items::TraitSolverLangItem::Iterator
            }
            hir_def::lang_item::LangItem::PinNewUnchecked => return None,
            hir_def::lang_item::LangItem::RangeFrom => return None,
            hir_def::lang_item::LangItem::RangeFull => return None,
            hir_def::lang_item::LangItem::RangeInclusiveStruct => return None,
            hir_def::lang_item::LangItem::RangeInclusiveNew => return None,
            hir_def::lang_item::LangItem::Range => return None,
            hir_def::lang_item::LangItem::RangeToInclusive => return None,
            hir_def::lang_item::LangItem::RangeTo => return None,
            hir_def::lang_item::LangItem::String => return None,
            hir_def::lang_item::LangItem::CStr => return None,
        })
    }

    fn associated_type_def_ids(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> impl IntoIterator<Item = <Self::Interner as rustc_type_ir::Interner>::DefId> {
        let trait_ = match def_id {
            GenericDefId::TraitId(id) => id,
            _ => unreachable!(),
        };
        let trait_data = self.db.trait_data(trait_);
        let associated_ty_ids: Vec<_> = trait_data.associated_types().map(|id| id.into()).collect();
        associated_ty_ids
    }

    fn for_each_relevant_impl(
        self,
        trait_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
        self_ty: <Self::Interner as rustc_type_ir::Interner>::Ty,
        mut f: impl FnMut(<Self::Interner as rustc_type_ir::Interner>::DefId),
    ) {
        let trait_ = match trait_def_id {
            GenericDefId::TraitId(id) => id,
            _ => panic!("for_each_relevant_impl called for non-trait"),
        };

        let self_ty_fp = TyFingerprint::for_trait_impl_ns(&self_ty);
        let fps: &[TyFingerprint] = match self_ty.clone().kind() {
            TyKind::Infer(InferTy::IntVar(..)) => &ALL_INT_FPS,
            TyKind::Infer(InferTy::FloatVar(..)) => &ALL_FLOAT_FPS,
            _ => self_ty_fp.as_ref().map(std::slice::from_ref).unwrap_or(&[]),
        };

        if fps.is_empty() {
            for_trait_impls(self.db, self.krate, self.block, trait_, self_ty_fp, |impls| {
                for i in impls.for_trait(trait_) {
                    f(GenericDefId::ImplId(i));
                }
                ControlFlow::Continue(())
            });
        } else {
            for_trait_impls(self.db, self.krate, self.block, trait_, self_ty_fp, |impls| {
                for fp in fps {
                    for i in impls.for_trait_and_self_ty(trait_, *fp) {
                        f(GenericDefId::ImplId(i));
                    }
                }
                ControlFlow::Continue(())
            });
        }
    }

    fn has_item_definition(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME: should check if has value
        true
    }

    fn impl_is_default(
        self,
        impl_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        false
    }

    fn impl_trait_ref(
        self,
        impl_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<Self::Interner, rustc_type_ir::TraitRef<Self::Interner>> {
        let impl_id = match impl_def_id {
            GenericDefId::ImplId(id) => id,
            _ => panic!("Unexpected GenericDefId in impl_trait_ref"),
        };

        let db = self.db;

        impl_trait_query(db, impl_id)
            // ImplIds for impls where the trait ref can't be resolved should never reach trait solving
            .expect("invalid impl passed to trait solver")
    }

    fn impl_polarity(
        self,
        impl_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::ImplPolarity {
        let impl_id = match impl_def_id {
            GenericDefId::ImplId(id) => id,
            _ => unreachable!(),
        };
        let impl_data = self.db.impl_data(impl_id);
        if impl_data.is_negative {
            ImplPolarity::Negative
        } else {
            ImplPolarity::Positive
        }
    }

    fn trait_is_auto(
        self,
        trait_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        let trait_ = match trait_def_id {
            GenericDefId::TraitId(id) => id,
            _ => panic!("Unexpected GenericDefId in trait_is_auto"),
        };
        let trait_data = self.db.trait_data(trait_);
        trait_data.flags.intersects(TraitFlags::IS_AUTO)
    }

    fn trait_is_alias(
        self,
        trait_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        matches!(trait_def_id, GenericDefId::TraitAliasId(_))
    }

    fn trait_is_dyn_compatible(
        self,
        trait_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        let trait_ = match trait_def_id {
            GenericDefId::TraitId(id) => id,
            _ => unreachable!(),
        };
        crate::dyn_compatibility::dyn_compatibility(self.db, trait_).is_none()
    }

    fn trait_is_fundamental(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        let trait_ = match def_id {
            GenericDefId::TraitId(id) => id,
            _ => panic!("Unexpected GenericDefId in trait_is_fundamental"),
        };
        let trait_data = self.db.trait_data(trait_);
        trait_data.flags.intersects(TraitFlags::IS_FUNDAMENTAL)
    }

    fn trait_may_be_implemented_via_object(
        self,
        trait_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        true
    }

    fn is_impl_trait_in_trait(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        false
    }

    fn delay_bug(
        self,
        msg: impl ToString,
    ) -> <Self::Interner as rustc_type_ir::Interner>::ErrorGuaranteed {
        todo!()
    }

    fn is_general_coroutine(
        self,
        coroutine_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        true
    }

    fn coroutine_is_async(
        self,
        coroutine_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        true
    }

    fn coroutine_is_gen(
        self,
        coroutine_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        false
    }

    fn coroutine_is_async_gen(
        self,
        coroutine_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        // FIXME
        false
    }

    fn unsizing_params_for_adt(
        self,
        adt_def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::UnsizingParams {
        let id = match adt_def_id {
            GenericDefId::AdtId(id) => id,
            _ => unreachable!(),
        };
        let def = AdtDef::new(id, self.db);
        let num_params = self.generics_of(adt_def_id).count();

        let maybe_unsizing_param_idx = |arg: GenericArg| match arg.kind() {
            GenericArgKind::Type(ty) => match ty.kind() {
                rustc_type_ir::TyKind::Param(p) => Some(p.index),
                _ => None,
            },
            GenericArgKind::Lifetime(_) => None,
            GenericArgKind::Const(ct) => match ct.kind() {
                rustc_type_ir::ConstKind::Param(p) => Some(p.index),
                _ => None,
            },
        };

        // The last field of the structure has to exist and contain type/const parameters.
        let variant = def.non_enum_variant();
        let fields = variant.fields(self.db);
        let Some((tail_field, prefix_fields)) = fields.split_last() else {
            return UnsizingParams(BitSet::new_empty(num_params));
        };

        let field_types = field_types_query(self.db, variant.id());
        let mut unsizing_params = BitSet::new_empty(num_params);
        let ty = field_types[tail_field.0].clone();
        for arg in ty.instantiate_identity().walk() {
            if let Some(i) = maybe_unsizing_param_idx(arg) {
                unsizing_params.insert(i);
            }
        }

        // Ensure none of the other fields mention the parameters used
        // in unsizing.
        for field in prefix_fields {
            for arg in field_types[field.0].clone().instantiate_identity().walk() {
                if let Some(i) = maybe_unsizing_param_idx(arg) {
                    unsizing_params.remove(i);
                }
            }
        }

        UnsizingParams(unsizing_params)
    }

    fn find_const_ty_from_env(
        self,
        param_env: &<Self::Interner as rustc_type_ir::Interner>::ParamEnv,
        placeholder: <Self::Interner as rustc_type_ir::Interner>::PlaceholderConst,
    ) -> <Self::Interner as rustc_type_ir::Interner>::Ty {
        todo!()
    }

    fn anonymize_bound_vars<T: rustc_type_ir::fold::TypeFoldable<Self::Interner>>(
        self,
        value: rustc_type_ir::Binder<Self::Interner, T>,
    ) -> rustc_type_ir::Binder<Self::Interner, T> {
        struct Anonymize<'a> {
            map: &'a mut FxIndexMap<BoundVar, BoundVarKind>,
        }
        impl BoundVarReplacerDelegate for Anonymize<'_> {
            fn replace_region(&mut self, br: BoundRegion) -> Region {
                let entry = self.map.entry(br.var);
                let index = entry.index();
                let var = BoundVar::from_usize(index);
                let kind = entry
                    .or_insert_with(|| BoundVarKind::Region(BoundRegionKind::Anon))
                    .clone()
                    .expect_region();
                let br = BoundRegion { var, kind };
                Region::new_bound(DbInterner, DebruijnIndex::ZERO, br)
            }
            fn replace_ty(&mut self, bt: BoundTy) -> Ty {
                let entry = self.map.entry(bt.var);
                let index = entry.index();
                let var = BoundVar::from_usize(index);
                let kind = entry
                    .or_insert_with(|| BoundVarKind::Ty(BoundTyKind::Anon))
                    .clone()
                    .expect_ty();
                Ty::new_bound(DbInterner, DebruijnIndex::ZERO, BoundTy { var, kind })
            }
            fn replace_const(&mut self, bv: BoundVar) -> Const {
                let entry = self.map.entry(bv);
                let index = entry.index();
                let var = BoundVar::from_usize(index);
                let () = entry.or_insert_with(|| BoundVarKind::Const).clone().expect_const();
                Const::new_bound(DbInterner, DebruijnIndex::ZERO, var)
            }
        }

        let mut map = Default::default();
        let delegate = Anonymize { map: &mut map };
        let inner = DbInterner.replace_escaping_bound_vars_uncached(value.skip_binder(), delegate);
        let bound_vars = CollectAndApply::collect_and_apply(map.into_values(), |xs| {
            BoundVarKinds::new_from_iter(xs.iter().cloned())
        });
        Binder::bind_with_vars(inner, bound_vars)
    }

    fn opaque_types_defined_by(
        self,
        defining_anchor: <Self::Interner as rustc_type_ir::Interner>::LocalDefId,
    ) -> <Self::Interner as rustc_type_ir::Interner>::DefiningOpaqueTypes {
        todo!()
    }

    fn alias_has_const_conditions(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> bool {
        todo!()
    }

    fn explicit_implied_const_bounds(
        self,
        def_id: <Self::Interner as rustc_type_ir::Interner>::DefId,
    ) -> rustc_type_ir::EarlyBinder<
        Self::Interner,
        impl IntoIterator<
            Item = rustc_type_ir::Binder<Self::Interner, rustc_type_ir::TraitRef<Self::Interner>>,
        >,
    > {
        rustc_type_ir::EarlyBinder::bind([todo!()])
    }

    fn fn_is_const(self, def_id: <Self::Interner as rustc_type_ir::Interner>::DefId) -> bool {
        todo!()
    }

    fn impl_is_const(self, def_id: <Self::Interner as rustc_type_ir::Interner>::DefId) -> bool {
        todo!()
    }
}

macro_rules! TrivialTypeTraversalImpls {
    ($($ty:ty,)+) => {
        $(
            impl rustc_type_ir::fold::TypeFoldable<DbInterner> for $ty {
                fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
                    self,
                    _: &mut F,
                ) -> ::std::result::Result<Self, F::Error> {
                    Ok(self)
                }

                #[inline]
                fn fold_with<F: rustc_type_ir::fold::TypeFolder<DbInterner>>(
                    self,
                    _: &mut F,
                ) -> Self {
                    self
                }
            }

            impl rustc_type_ir::visit::TypeVisitable<DbInterner> for $ty {
                #[inline]
                fn visit_with<F: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
                    &self,
                    _: &mut F)
                    -> F::Result
                {
                    <F::Result as rustc_ast_ir::visit::VisitorResult>::output()
                }
            }
        )+
    };
}

TrivialTypeTraversalImpls! {
    GenericDefId,
    PatId,
    Safety,
    FnAbi,
    Span,
    ParamConst,
    ParamTy,
    BoundRegion,
    BoundVar,
    Placeholder<BoundRegion>,
    Placeholder<BoundTy>,
    Placeholder<BoundVar>,
    ValueConst,
    Reveal,
}

pub mod tls {
    scoped_tls::scoped_thread_local!(static DB: *const dyn crate::db::HirDatabase);

    pub fn with_db<T>(db: &dyn crate::db::HirDatabase, f: impl FnOnce() -> T) -> T {
        DB.set(
            &(unsafe { std::mem::transmute::<_, &'static dyn crate::db::HirDatabase>(db) }
                as *const dyn crate::db::HirDatabase),
            f,
        )
    }

    impl super::DbInterner {
        pub(super) fn with_db<T>(self, f: impl FnOnce(&dyn crate::db::HirDatabase) -> T) -> T {
            DB.with(move |slot| f(unsafe { &**slot }))
        }
    }

    pub fn with_db_out_of_thin_air<T>(f: impl FnOnce(&dyn crate::db::HirDatabase) -> T) -> T {
        DB.with(move |slot| f(unsafe { &**slot }))
    }

    pub fn with_opt_db_out_of_thin_air<T>(
        f: impl FnOnce(Option<&dyn crate::db::HirDatabase>) -> T,
    ) -> T {
        if DB.is_set() {
            DB.with(move |slot| f(Some(unsafe { &**slot })))
        } else {
            f(None)
        }
    }
}
