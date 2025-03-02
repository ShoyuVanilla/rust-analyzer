use std::iter;
use std::ops::{self, ControlFlow};

use base_db::CrateId;
use extension_traits::extension;
use hir_def::{BlockId, HasModule};
use rustc_abi::{Float, HasDataLayout, Integer, IntegerType, Primitive, ReprOptions};
use rustc_type_ir::data_structures::IndexMap;
use rustc_type_ir::fold::TypeFoldable;
use rustc_type_ir::inherent::{GenericArg as _, IrAdtDef, SliceLike};
use rustc_type_ir::{
    fold::{TypeFolder, TypeSuperFoldable},
    inherent::IntoKind,
    visit::{TypeSuperVisitable, TypeVisitor},
    ConstKind, CoroutineArgs, FloatTy, IntTy, RegionKind, UintTy, UniverseIndex,
};
use rustc_type_ir::{BoundVar, Canonical, DebruijnIndex, EarlyBinder, GenericArgKind};

use crate::{
    db::HirDatabase,
    from_foreign_def_id,
    method_resolution::{TraitImpls, TyFingerprint},
};

use super::fold::{BoundVarReplacer, FnMutDelegate};
use super::{
    Binder, BoundRegion, BoundTy, CanonicalVarInfo, CanonicalVars, Clause, Const, DbInterner, DbIr,
    GenericArg, GenericArgs, Region, Ty, TyKind,
};

#[derive(Clone, Debug)]
pub struct Discr {
    /// Bit representation of the discriminant (e.g., `-128i8` is `0xFF_u128`).
    pub val: u128,
    pub ty: Ty,
}

impl Discr {
    /// Adds `1` to the value and wraps around if the maximum for the type is reached.
    pub fn wrap_incr(self, interner: DbInterner) -> Self {
        self.checked_add(interner, 1).0
    }
    pub fn checked_add(self, interner: DbInterner, n: u128) -> (Self, bool) {
        let (size, signed) = self.ty.clone().int_size_and_signed(interner);
        let (val, oflo) = if signed {
            let min = size.signed_int_min();
            let max = size.signed_int_max();
            let val = size.sign_extend(self.val);
            assert!(n < (i128::MAX as u128));
            let n = n as i128;
            let oflo = val > max - n;
            let val = if oflo { min + (n - (max - val) - 1) } else { val + n };
            // zero the upper bits
            let val = val as u128;
            let val = size.truncate(val);
            (val, oflo)
        } else {
            let max = size.unsigned_int_max();
            let val = self.val;
            let oflo = val > max - n;
            let val = if oflo { n - (max - val) - 1 } else { val + n };
            (val, oflo)
        };
        (Self { val, ty: self.ty }, oflo)
    }
}

#[extension(pub trait IntegerTypeExt)]
impl IntegerType {
    fn to_ty(&self, interner: DbInterner) -> Ty {
        match self {
            IntegerType::Pointer(true) => Ty::new(TyKind::Int(IntTy::Isize)),
            IntegerType::Pointer(false) => Ty::new(TyKind::Uint(UintTy::Usize)),
            IntegerType::Fixed(i, s) => i.to_ty(interner, *s),
        }
    }

    fn initial_discriminant(&self, interner: DbInterner) -> Discr {
        Discr { val: 0, ty: self.to_ty(interner) }
    }

    fn disr_incr(&self, interner: DbInterner, val: Option<Discr>) -> Option<Discr> {
        if let Some(val) = val {
            assert_eq!(self.to_ty(interner), val.ty);
            let (new, oflo) = val.checked_add(interner, 1);
            if oflo {
                None
            } else {
                Some(new)
            }
        } else {
            Some(self.initial_discriminant(interner))
        }
    }
}

#[extension(pub trait IntegerExt)]
impl Integer {
    #[inline]
    fn to_ty(&self, interner: DbInterner, signed: bool) -> Ty {
        use Integer::*;
        match (*self, signed) {
            (I8, false) => Ty::new(TyKind::Uint(UintTy::U8)),
            (I16, false) => Ty::new(TyKind::Uint(UintTy::U16)),
            (I32, false) => Ty::new(TyKind::Uint(UintTy::U32)),
            (I64, false) => Ty::new(TyKind::Uint(UintTy::U64)),
            (I128, false) => Ty::new(TyKind::Uint(UintTy::U128)),
            (I8, true) => Ty::new(TyKind::Int(IntTy::I8)),
            (I16, true) => Ty::new(TyKind::Int(IntTy::I16)),
            (I32, true) => Ty::new(TyKind::Int(IntTy::I32)),
            (I64, true) => Ty::new(TyKind::Int(IntTy::I64)),
            (I128, true) => Ty::new(TyKind::Int(IntTy::I128)),
        }
    }

    fn from_int_ty<C: HasDataLayout>(cx: &C, ity: IntTy) -> Integer {
        use Integer::*;
        match ity {
            IntTy::I8 => I8,
            IntTy::I16 => I16,
            IntTy::I32 => I32,
            IntTy::I64 => I64,
            IntTy::I128 => I128,
            IntTy::Isize => cx.data_layout().ptr_sized_integer(),
        }
    }
    fn from_uint_ty<C: HasDataLayout>(cx: &C, ity: UintTy) -> Integer {
        use Integer::*;
        match ity {
            UintTy::U8 => I8,
            UintTy::U16 => I16,
            UintTy::U32 => I32,
            UintTy::U64 => I64,
            UintTy::U128 => I128,
            UintTy::Usize => cx.data_layout().ptr_sized_integer(),
        }
    }

    /// Finds the appropriate Integer type and signedness for the given
    /// signed discriminant range and `#[repr]` attribute.
    /// N.B.: `u128` values above `i128::MAX` will be treated as signed, but
    /// that shouldn't affect anything, other than maybe debuginfo.
    fn repr_discr(
        interner: DbInterner,
        ty: Ty,
        repr: &ReprOptions,
        min: i128,
        max: i128,
    ) -> (Integer, bool) {
        // Theoretically, negative values could be larger in unsigned representation
        // than the unsigned representation of the signed minimum. However, if there
        // are any negative values, the only valid unsigned representation is u128
        // which can fit all i128 values, so the result remains unaffected.
        let unsigned_fit = Integer::fit_unsigned(std::cmp::max(min as u128, max as u128));
        let signed_fit = std::cmp::max(Integer::fit_signed(min), Integer::fit_signed(max));

        if let Some(ity) = repr.int {
            let discr = Integer::from_attr(&interner, ity);
            let fit = if ity.is_signed() { signed_fit } else { unsigned_fit };
            if discr < fit {
                panic!(
                    "Integer::repr_discr: `#[repr]` hint too small for \
                      discriminant range of enum `{:?}`",
                    ty
                )
            }
            return (discr, ity.is_signed());
        }

        let at_least = if repr.c() {
            // This is usually I32, however it can be different on some platforms,
            // notably hexagon and arm-none/thumb-none
            interner.data_layout().c_enum_min_size
        } else {
            // repr(Rust) enums try to be as small as possible
            Integer::I8
        };

        // If there are no negative values, we can use the unsigned fit.
        if min >= 0 {
            (std::cmp::max(unsigned_fit, at_least), false)
        } else {
            (std::cmp::max(signed_fit, at_least), true)
        }
    }
}

#[extension(pub trait FloatExt)]
impl Float {
    #[inline]
    fn to_ty(&self, interner: DbInterner) -> Ty {
        use Float::*;
        match *self {
            F16 => Ty::new(TyKind::Float(FloatTy::F16)),
            F32 => Ty::new(TyKind::Float(FloatTy::F32)),
            F64 => Ty::new(TyKind::Float(FloatTy::F64)),
            F128 => Ty::new(TyKind::Float(FloatTy::F128)),
        }
    }

    fn from_float_ty(fty: FloatTy) -> Self {
        use Float::*;
        match fty {
            FloatTy::F16 => F16,
            FloatTy::F32 => F32,
            FloatTy::F64 => F64,
            FloatTy::F128 => F128,
        }
    }
}

#[extension(pub trait PrimitiveExt)]
impl Primitive {
    #[inline]
    fn to_ty(&self, interner: DbInterner) -> Ty {
        match *self {
            Primitive::Int(i, signed) => i.to_ty(interner, signed),
            Primitive::Float(f) => f.to_ty(interner),
            Primitive::Pointer(_) => Ty::new(TyKind::RawPtr(
                Ty::new(TyKind::Tuple(Default::default())),
                rustc_ast_ir::Mutability::Mut,
            )),
        }
    }

    /// Return an *integer* type matching this primitive.
    /// Useful in particular when dealing with enum discriminants.
    #[inline]
    fn to_int_ty(&self, interner: DbInterner) -> Ty {
        match *self {
            Primitive::Int(i, signed) => i.to_ty(interner, signed),
            Primitive::Pointer(_) => {
                let signed = false;
                interner.data_layout().ptr_sized_integer().to_ty(interner, signed)
            }
            Primitive::Float(_) => panic!("floats do not have an int type"),
        }
    }
}

impl HasDataLayout for DbInterner {
    fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
        todo!()
    }
}

#[extension(pub trait CoroutineArgsExt)]
impl CoroutineArgs<DbInterner> {
    /// The type of the state discriminant used in the coroutine type.
    #[inline]
    fn discr_ty(&self, interner: DbInterner) -> Ty {
        Ty::new(TyKind::Uint(UintTy::U32))
    }
}

/// Finds the max universe present
pub struct MaxUniverse {
    max_universe: UniverseIndex,
}

impl MaxUniverse {
    pub fn new() -> Self {
        MaxUniverse { max_universe: UniverseIndex::ROOT }
    }

    pub fn max_universe(self) -> UniverseIndex {
        self.max_universe
    }
}

impl TypeVisitor<DbInterner> for MaxUniverse {
    type Result = ();

    fn visit_ty(&mut self, t: Ty) {
        if let TyKind::Placeholder(placeholder) = t.clone().kind() {
            self.max_universe = UniverseIndex::from_u32(
                self.max_universe.as_u32().max(placeholder.universe.as_u32()),
            );
        }

        t.super_visit_with(self)
    }

    fn visit_const(&mut self, c: Const) {
        if let ConstKind::Placeholder(placeholder) = c.clone().kind() {
            self.max_universe = UniverseIndex::from_u32(
                self.max_universe.as_u32().max(placeholder.universe.as_u32()),
            );
        }

        c.super_visit_with(self)
    }

    fn visit_region(&mut self, r: Region) {
        if let RegionKind::RePlaceholder(placeholder) = r.kind() {
            self.max_universe = UniverseIndex::from_u32(
                self.max_universe.as_u32().max(placeholder.universe.as_u32()),
            );
        }
    }
}

pub struct BottomUpFolder<F, G, H>
where
    F: FnMut(Ty) -> Ty,
    G: FnMut(Region) -> Region,
    H: FnMut(Const) -> Const,
{
    pub interner: DbInterner,
    pub ty_op: F,
    pub lt_op: G,
    pub ct_op: H,
}

impl<F, G, H> TypeFolder<DbInterner> for BottomUpFolder<F, G, H>
where
    F: FnMut(Ty) -> Ty,
    G: FnMut(Region) -> Region,
    H: FnMut(Const) -> Const,
{
    fn cx(&self) -> DbInterner {
        self.interner
    }

    fn fold_ty(&mut self, ty: Ty) -> Ty {
        let t = ty.super_fold_with(self);
        (self.ty_op)(t)
    }

    fn fold_region(&mut self, r: Region) -> Region {
        // This one is a little different, because `super_fold_with` is not
        // implemented on non-recursive `Region`.
        (self.lt_op)(r)
    }

    fn fold_const(&mut self, ct: Const) -> Const {
        let ct = ct.super_fold_with(self);
        (self.ct_op)(ct)
    }
}

pub(crate) fn for_trait_impls(
    db: &dyn HirDatabase,
    krate: CrateId,
    block: Option<BlockId>,
    trait_id: hir_def::TraitId,
    self_ty_fp: Option<TyFingerprint>,
    mut f: impl FnMut(&TraitImpls) -> ControlFlow<()>,
) -> ControlFlow<()> {
    // Note: Since we're using `impls_for_trait` and `impl_provided_for`,
    // only impls where the trait can be resolved should ever reach Chalk.
    // `impl_datum` relies on that and will panic if the trait can't be resolved.
    let in_deps = db.trait_impls_in_deps(krate);
    let in_self = db.trait_impls_in_crate(krate);
    let trait_module = trait_id.module(db.upcast());
    let type_module = match self_ty_fp {
        Some(TyFingerprint::Adt(adt_id)) => Some(adt_id.module(db.upcast())),
        Some(TyFingerprint::ForeignType(type_id)) => {
            Some(from_foreign_def_id(type_id).module(db.upcast()))
        }
        Some(TyFingerprint::Dyn(trait_id)) => Some(trait_id.module(db.upcast())),
        _ => None,
    };

    let mut def_blocks =
        [trait_module.containing_block(), type_module.and_then(|it| it.containing_block())];

    let block_impls = iter::successors(block, |&block_id| {
        cov_mark::hit!(block_local_impls);
        db.block_def_map(block_id).parent().and_then(|module| module.containing_block())
    })
    .inspect(|&block_id| {
        // make sure we don't search the same block twice
        def_blocks.iter_mut().for_each(|block| {
            if *block == Some(block_id) {
                *block = None;
            }
        });
    })
    .filter_map(|block_id| db.trait_impls_in_block(block_id));
    f(&in_self)?;
    for it in in_deps.iter().map(ops::Deref::deref) {
        f(it)?;
    }
    for it in block_impls {
        f(&it)?;
    }
    for it in def_blocks.into_iter().flatten().filter_map(|it| db.trait_impls_in_block(it)) {
        f(&it)?;
    }
    ControlFlow::Continue(())
}

#[tracing::instrument(level = "debug", skip(ir), ret)]
pub fn sized_constraint_for_ty(ir: DbIr<'_>, ty: Ty) -> Option<Ty> {
    use rustc_type_ir::TyKind::*;

    match ty.clone().kind() {
        // these are always sized
        Bool
        | Char
        | Int(..)
        | Uint(..)
        | Float(..)
        | RawPtr(..)
        | Ref(..)
        | FnDef(..)
        | FnPtr(..)
        | Array(..)
        | Closure(..)
        | CoroutineClosure(..)
        | Coroutine(..)
        | CoroutineWitness(..)
        | Never
        | Dynamic(_, _, rustc_type_ir::DynKind::DynStar) => None,

        // these are never sized
        Str | Slice(..) | Dynamic(_, _, rustc_type_ir::DynKind::Dyn) | Foreign(..) => Some(ty),

        Pat(ty, _) => sized_constraint_for_ty(ir, ty),

        Tuple(tys) => tys.into_iter().last().and_then(|ty| sized_constraint_for_ty(ir, ty)),

        // recursive case
        Adt(adt, args) => {
            let tail_ty =
                EarlyBinder::bind(adt.all_field_tys(ir).skip_binder().into_iter().last()?)
                    .instantiate(DbInterner, args);
            sized_constraint_for_ty(ir, tail_ty)
        }

        // these can be sized or unsized
        Param(..) | Alias(..) | Error(_) => Some(ty),

        Placeholder(..) | Bound(..) | Infer(..) => {
            panic!("unexpected type `{ty:?}` in sized_constraint_for_ty")
        }
    }
}

pub fn apply_args_to_binder<T: TypeFoldable<DbInterner>>(
    b: Binder<T>,
    args: GenericArgs,
    db: &dyn HirDatabase,
) -> T {
    // An Ir is needed for debug_asserting args compatible in Alias creation - it's just a noop for us so we can give fake data for CrateId and Block
    let fake_ir =
        crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let types = &mut |ty: BoundTy| args.as_slice()[ty.var.index()].expect_ty();
    let regions = &mut |region: BoundRegion| args.as_slice()[region.var.index()].expect_region();
    let consts = &mut |const_: BoundVar| args.as_slice()[const_.index()].expect_const();
    let mut instantiate =
        BoundVarReplacer::new(DbInterner, FnMutDelegate { types, regions, consts });
    b.skip_binder().fold_with(&mut instantiate)
}

pub fn mini_canonicalize<T: TypeFoldable<DbInterner>>(val: T) -> Canonical<DbInterner, T> {
    let mut canon = MiniCanonicalizer { db: DebruijnIndex::ZERO, vars: IndexMap::default() };
    let canon_val = val.fold_with(&mut canon);
    Canonical {
        value: canon_val,
        max_universe: UniverseIndex::from_u32(1),
        variables: CanonicalVars::new_from_iter(canon.vars.iter().map(|(k, v)| {
            let kind = match k.clone().kind() {
                GenericArgKind::Type(ty) => match ty.kind() {
                    TyKind::Int(..) | TyKind::Uint(..) => {
                        rustc_type_ir::CanonicalVarKind::Ty(rustc_type_ir::CanonicalTyVarKind::Int)
                    }
                    TyKind::Float(..) => rustc_type_ir::CanonicalVarKind::Ty(
                        rustc_type_ir::CanonicalTyVarKind::Float,
                    ),
                    _ => rustc_type_ir::CanonicalVarKind::Ty(
                        rustc_type_ir::CanonicalTyVarKind::General(UniverseIndex::ZERO),
                    ),
                },
                GenericArgKind::Lifetime(_) => {
                    rustc_type_ir::CanonicalVarKind::Region(UniverseIndex::ZERO)
                }
                GenericArgKind::Const(_) => {
                    rustc_type_ir::CanonicalVarKind::Const(UniverseIndex::ZERO)
                }
            };
            CanonicalVarInfo { kind }
        })),
    }
}

struct MiniCanonicalizer {
    db: DebruijnIndex,
    vars: IndexMap<GenericArg, usize>,
}

impl TypeFolder<DbInterner> for MiniCanonicalizer {
    fn cx(&self) -> DbInterner {
        DbInterner
    }

    fn fold_binder<T: TypeFoldable<DbInterner>>(
        &mut self,
        t: rustc_type_ir::Binder<DbInterner, T>,
    ) -> rustc_type_ir::Binder<DbInterner, T> {
        self.db.shift_in(1);
        let res = t.map_bound(|t| t.fold_with(self));
        self.db.shift_out(1);
        res
    }

    fn fold_ty(&mut self, t: Ty) -> Ty {
        match t.clone().kind() {
            rustc_type_ir::TyKind::Bound(db, _) => {
                if db >= self.db {
                    panic!("Unexpected bound var");
                }
                t
            }
            rustc_type_ir::TyKind::Infer(infer) => {
                let len = self.vars.len();
                let var = *self.vars.entry(t.into()).or_insert(len);
                Ty::new(TyKind::Bound(
                    self.db,
                    BoundTy { kind: super::BoundTyKind::Anon, var: BoundVar::from_usize(var) },
                ))
            }
            _ => t.super_fold_with(self),
        }
    }

    fn fold_region(
        &mut self,
        r: <DbInterner as rustc_type_ir::Interner>::Region,
    ) -> <DbInterner as rustc_type_ir::Interner>::Region {
        match r.clone().kind() {
            RegionKind::ReBound(db, _) => {
                if db >= self.db {
                    panic!("Unexpected bound var");
                }
                r
            }
            RegionKind::ReVar(vid) => {
                let len = self.vars.len();
                let var = *self.vars.entry(r.into()).or_insert(len);
                Region::new(RegionKind::ReBound(
                    self.db,
                    BoundRegion {
                        kind: super::BoundRegionKind::Anon,
                        var: BoundVar::from_usize(len),
                    },
                ))
            }
            _ => r,
        }
    }

    fn fold_const(
        &mut self,
        c: <DbInterner as rustc_type_ir::Interner>::Const,
    ) -> <DbInterner as rustc_type_ir::Interner>::Const {
        match c.clone().kind() {
            ConstKind::Bound(db, _) => {
                if db >= self.db {
                    panic!("Unexpected bound var");
                }
                c
            }
            ConstKind::Infer(infer) => {
                let len = self.vars.len();
                let var = *self.vars.entry(c.into()).or_insert(len);
                Const::new(ConstKind::Bound(self.db, BoundVar::from_usize(len)))
            }
            _ => c.super_fold_with(self),
        }
    }
}
