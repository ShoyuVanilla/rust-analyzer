use hir_def::GenericDefId;
use intern::{Interned, Symbol};
use rustc_abi::{Float, Integer, Size};
use rustc_ast_ir::{try_visit, visit::VisitorResult};
use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable}, inherent::{BoundVarLike, GenericArgs as _, IntoKind, ParamLike, PlaceholderLike, SliceLike}, relate::Relate, visit::{Flags, TypeSuperVisitable, TypeVisitable}, BoundVar, ClosureKind, FloatTy, FloatVid, InferTy, IntTy, IntVid, UintTy, WithCachedTypeInfo
};
use smallvec::SmallVec;

use crate::{
    interner::InternedWrapper,
    next_solver::util::{CoroutineArgsExt, IntegerTypeExt},
};

use super::{
    flags::FlagComputation,
    interned_vec,
    util::{FloatExt, IntegerExt},
    BoundVarKind, DbInterner, GenericArgs, Placeholder,
};

pub type TyKind = rustc_type_ir::TyKind<DbInterner>;
pub type FnHeader = rustc_type_ir::FnHeader<DbInterner>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Ty(Interned<InternedWrapper<WithCachedTypeInfo<TyKind>>>);

impl Ty {
    pub fn new(kind: TyKind) -> Self {
        let flags = FlagComputation::for_kind(&kind);
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Ty(Interned::new(InternedWrapper(cached)))
    }

    pub fn new_param(index: u32, name: Symbol) -> Self {
        Ty::new(TyKind::Param(ParamTy { index, name }))
    }

    pub fn new_placeholder(placeholder: PlaceholderTy) -> Ty {
        Ty::new(TyKind::Placeholder(placeholder))
    }

    pub fn new_infer(infer: InferTy) -> Ty {
        Ty::new(TyKind::Infer(infer))
    }

    pub fn new_int_var(v: IntVid) -> Ty {
        Ty::new_infer(InferTy::IntVar(v))
    }

    pub fn new_float_var(v: FloatVid) -> Ty {
        Ty::new_infer(InferTy::FloatVar(v))
    }

    pub fn new_int(i: IntTy) -> Ty {
        Ty::new(TyKind::Int(i))
    }

    pub fn new_uint(ui: UintTy) -> Ty {
        Ty::new(TyKind::Uint(ui))
    }

    pub fn new_float(f: FloatTy) -> Ty {
        Ty::new(TyKind::Float(f))
    }

    pub fn new_fresh(n: u32) -> Ty {
        Ty::new_infer(InferTy::FreshTy(n))
    }

    pub fn new_fresh_int(n: u32) -> Ty {
        Ty::new_infer(InferTy::FreshIntTy(n))
    }

    pub fn new_fresh_float(n: u32) -> Ty {
        Ty::new_infer(InferTy::FreshFloatTy(n))
    }
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0 .0.internee.fmt(f)
    }
}

interned_vec!(Tys, Ty);

impl rustc_type_ir::inherent::Tys<DbInterner> for Tys {
    fn inputs(self) -> <DbInterner as rustc_type_ir::Interner>::FnInputTys {
        Tys::new_from_iter(self.as_slice().split_last().unwrap().1.iter().cloned())
    }

    fn output(self) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        self.as_slice().split_last().unwrap().0.clone()
    }
}

pub type PlaceholderTy = Placeholder<BoundTy>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug by hand
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

impl ParamTy {
    pub fn to_ty(self) -> Ty {
        Ty::new_param(self.index, self.name)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug by hand
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoundTyKind {
    Anon,
    Param(GenericDefId, Symbol),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ErrorGuaranteed;

impl IntoKind for Ty {
    type Kind = TyKind;

    fn kind(self) -> Self::Kind {
        self.0 .0.internee.clone()
    }
}

impl TypeVisitable<DbInterner> for ErrorGuaranteed {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_error(*self)
    }
}

impl TypeFoldable<DbInterner> for ErrorGuaranteed {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
}

impl TypeVisitable<DbInterner> for Ty {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_ty(self.clone())
    }
}

impl TypeSuperVisitable<DbInterner> for Ty {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self.clone().kind() {
            TyKind::RawPtr(ty, _mutbl) => ty.visit_with(visitor),
            TyKind::Array(typ, sz) => {
                try_visit!(typ.visit_with(visitor));
                sz.visit_with(visitor)
            }
            TyKind::Slice(typ) => typ.visit_with(visitor),
            TyKind::Adt(_, args) => args.visit_with(visitor),
            TyKind::Dynamic(ref trait_ty, ref reg, _) => {
                try_visit!(trait_ty.visit_with(visitor));
                reg.visit_with(visitor)
            }
            TyKind::Tuple(ts) => ts.visit_with(visitor),
            TyKind::FnDef(_, args) => args.visit_with(visitor),
            TyKind::FnPtr(ref sig_tys, _) => sig_tys.visit_with(visitor),
            TyKind::Ref(r, ty, _) => {
                try_visit!(r.visit_with(visitor));
                ty.visit_with(visitor)
            }
            TyKind::Coroutine(_did, ref args) => args.visit_with(visitor),
            TyKind::CoroutineWitness(_did, ref args) => args.visit_with(visitor),
            TyKind::Closure(_did, ref args) => args.visit_with(visitor),
            TyKind::CoroutineClosure(_did, ref args) => args.visit_with(visitor),
            TyKind::Alias(_, ref data) => data.visit_with(visitor),

            TyKind::Pat(ty, pat) => {
                try_visit!(ty.visit_with(visitor));
                pat.visit_with(visitor)
            }

            TyKind::Error(guar) => guar.visit_with(visitor),

            TyKind::Bool
            | TyKind::Char
            | TyKind::Str
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Infer(_)
            | TyKind::Bound(..)
            | TyKind::Placeholder(..)
            | TyKind::Param(..)
            | TyKind::Never
            | TyKind::Foreign(..) => V::Result::output(),
        }
    }
}

impl TypeFoldable<DbInterner> for Ty {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_ty(self)
    }
}

impl TypeSuperFoldable<DbInterner> for Ty {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let kind = match self.clone().kind() {
            TyKind::RawPtr(ty, mutbl) => TyKind::RawPtr(ty.try_fold_with(folder)?, mutbl),
            TyKind::Array(typ, sz) => {
                TyKind::Array(typ.try_fold_with(folder)?, sz.try_fold_with(folder)?)
            }
            TyKind::Slice(typ) => TyKind::Slice(typ.try_fold_with(folder)?),
            TyKind::Adt(tid, args) => TyKind::Adt(tid, args.try_fold_with(folder)?),
            TyKind::Dynamic(trait_ty, region, representation) => TyKind::Dynamic(
                trait_ty.try_fold_with(folder)?,
                region.try_fold_with(folder)?,
                representation,
            ),
            TyKind::Tuple(ts) => TyKind::Tuple(ts.try_fold_with(folder)?),
            TyKind::FnDef(def_id, args) => TyKind::FnDef(def_id, args.try_fold_with(folder)?),
            TyKind::FnPtr(sig_tys, hdr) => TyKind::FnPtr(sig_tys.try_fold_with(folder)?, hdr),
            TyKind::Ref(r, ty, mutbl) => {
                TyKind::Ref(r.try_fold_with(folder)?, ty.try_fold_with(folder)?, mutbl)
            }
            TyKind::Coroutine(did, args) => TyKind::Coroutine(did, args.try_fold_with(folder)?),
            TyKind::CoroutineWitness(did, args) => {
                TyKind::CoroutineWitness(did, args.try_fold_with(folder)?)
            }
            TyKind::Closure(did, args) => TyKind::Closure(did, args.try_fold_with(folder)?),
            TyKind::CoroutineClosure(did, args) => {
                TyKind::CoroutineClosure(did, args.try_fold_with(folder)?)
            }
            TyKind::Alias(kind, data) => TyKind::Alias(kind, data.try_fold_with(folder)?),
            TyKind::Pat(ty, pat) => {
                TyKind::Pat(ty.try_fold_with(folder)?, pat.try_fold_with(folder)?)
            }

            TyKind::Bool
            | TyKind::Char
            | TyKind::Str
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Error(_)
            | TyKind::Infer(_)
            | TyKind::Param(..)
            | TyKind::Bound(..)
            | TyKind::Placeholder(..)
            | TyKind::Never
            | TyKind::Foreign(..) => return Ok(self),
        };

        Ok(if self.clone().kind() == kind { self } else { Ty::new(kind) })
    }
}

impl Relate<DbInterner> for Ty {
    fn relate<R: rustc_type_ir::relate::TypeRelation<I = DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        relation.tys(a, b)
    }
}

impl Flags for Ty {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.0.flags
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.0.outer_exclusive_binder
    }
}

impl rustc_type_ir::inherent::Ty<DbInterner> for Ty {
    fn new_unit(interner: DbInterner) -> Self {
        Ty::new(TyKind::Tuple(Default::default()))
    }

    fn new_bool(interner: DbInterner) -> Self {
        Ty::new(TyKind::Bool)
    }

    fn new_u8(interner: DbInterner) -> Self {
        Ty::new(TyKind::Uint(rustc_type_ir::UintTy::U8))
    }

    fn new_usize(interner: DbInterner) -> Self {
        Ty::new(TyKind::Uint(rustc_type_ir::UintTy::Usize))
    }

    fn new_infer(interner: DbInterner, var: rustc_type_ir::InferTy) -> Self {
        Ty::new(TyKind::Infer(var))
    }

    fn new_var(interner: DbInterner, var: rustc_type_ir::TyVid) -> Self {
        Ty::new(TyKind::Infer(rustc_type_ir::InferTy::TyVar(var)))
    }

    fn new_param(interner: DbInterner, param: ParamTy) -> Self {
        Ty::new(TyKind::Param(param))
    }

    fn new_placeholder(interner: DbInterner, param: PlaceholderTy) -> Self {
        Ty::new(TyKind::Placeholder(param))
    }

    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundTy,
    ) -> Self {
        Ty::new(TyKind::Bound(debruijn, var))
    }

    fn new_anon_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundVar,
    ) -> Self {
        Ty::new(TyKind::Bound(debruijn, BoundTy { var, kind: BoundTyKind::Anon }))
    }

    fn new_alias(
        interner: DbInterner,
        kind: rustc_type_ir::AliasTyKind,
        alias_ty: rustc_type_ir::AliasTy<DbInterner>,
    ) -> Self {
        Ty::new(TyKind::Alias(kind, alias_ty))
    }

    fn new_error(interner: DbInterner, guar: ErrorGuaranteed) -> Self {
        Ty::new(TyKind::Error(guar))
    }

    fn new_adt(
        interner: DbInterner,
        adt_def: <DbInterner as rustc_type_ir::Interner>::AdtDef,
        args: GenericArgs,
    ) -> Self {
        Ty::new(TyKind::Adt(adt_def, args))
    }

    fn new_foreign(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
    ) -> Self {
        Ty::new(TyKind::Foreign(def_id))
    }

    fn new_dynamic(
        interner: DbInterner,
        preds: <DbInterner as rustc_type_ir::Interner>::BoundExistentialPredicates,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        kind: rustc_type_ir::DynKind,
    ) -> Self {
        Ty::new(TyKind::Dynamic(preds, region, kind))
    }

    fn new_coroutine(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        Ty::new(TyKind::Coroutine(def_id, args))
    }

    fn new_coroutine_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        Ty::new(TyKind::CoroutineClosure(def_id, args))
    }

    fn new_closure(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        Ty::new(TyKind::Closure(def_id, args))
    }

    fn new_coroutine_witness(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        Ty::new(TyKind::CoroutineWitness(def_id, args))
    }

    fn new_ptr(interner: DbInterner, ty: Self, mutbl: rustc_ast_ir::Mutability) -> Self {
        Ty::new(TyKind::RawPtr(ty, mutbl))
    }

    fn new_ref(
        interner: DbInterner,
        region: <DbInterner as rustc_type_ir::Interner>::Region,
        ty: Self,
        mutbl: rustc_ast_ir::Mutability,
    ) -> Self {
        Ty::new(TyKind::Ref(region, ty, mutbl))
    }

    fn new_array_with_const_len(
        interner: DbInterner,
        ty: Self,
        len: <DbInterner as rustc_type_ir::Interner>::Const,
    ) -> Self {
        Ty::new(TyKind::Array(ty, len))
    }

    fn new_slice(interner: DbInterner, ty: Self) -> Self {
        Ty::new(TyKind::Slice(ty))
    }

    fn new_tup(interner: DbInterner, tys: &[<DbInterner as rustc_type_ir::Interner>::Ty]) -> Self {
        Ty::new(TyKind::Tuple(Tys::new_from_iter(tys.iter().cloned())))
    }

    fn new_tup_from_iter<It, T>(interner: DbInterner, iter: It) -> T::Output
    where
        It: Iterator<Item = T>,
        T: rustc_type_ir::CollectAndApply<Self, Self>,
    {
        T::collect_and_apply(iter, |ts| Ty::new_tup(interner, ts))
    }

    fn new_fn_def(
        interner: DbInterner,
        def_id: <DbInterner as rustc_type_ir::Interner>::DefId,
        args: <DbInterner as rustc_type_ir::Interner>::GenericArgs,
    ) -> Self {
        Ty::new(TyKind::FnDef(def_id, args))
    }

    fn new_fn_ptr(
        interner: DbInterner,
        sig: rustc_type_ir::Binder<DbInterner, rustc_type_ir::FnSig<DbInterner>>,
    ) -> Self {
        let (sig_tys, header) = sig.split();
        Ty::new(TyKind::FnPtr(sig_tys, header))
    }

    fn new_pat(
        interner: DbInterner,
        ty: Self,
        pat: <DbInterner as rustc_type_ir::Interner>::Pat,
    ) -> Self {
        Ty::new(TyKind::Pat(ty, pat))
    }

    fn tuple_fields(self) -> <DbInterner as rustc_type_ir::Interner>::Tys {
        match self.clone().kind() {
            TyKind::Tuple(args) => args,
            _ => panic!("tuple_fields called on non-tuple: {self:?}"),
        }
    }

    fn to_opt_closure_kind(self) -> Option<rustc_type_ir::ClosureKind> {
        match self.clone().kind() {
            TyKind::Int(int_ty) => match int_ty {
                IntTy::I8 => Some(ClosureKind::Fn),
                IntTy::I16 => Some(ClosureKind::FnMut),
                IntTy::I32 => Some(ClosureKind::FnOnce),
                _ => unreachable!("cannot convert type `{:?}` to a closure kind", self),
            },

            // "Bound" types appear in canonical queries when the
            // closure type is not yet known, and `Placeholder` and `Param`
            // may be encountered in generic `AsyncFnKindHelper` goals.
            TyKind::Bound(..) | TyKind::Placeholder(_) | TyKind::Param(_) | TyKind::Infer(_) => {
                None
            }

            TyKind::Error(_) => Some(ClosureKind::Fn),

            _ => unreachable!("cannot convert type `{:?}` to a closure kind", self),
        }
    }

    fn from_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        match kind {
            ClosureKind::Fn => Ty::new(TyKind::Int(IntTy::I8)),
            ClosureKind::FnMut => Ty::new(TyKind::Int(IntTy::I16)),
            ClosureKind::FnOnce => Ty::new(TyKind::Int(IntTy::I32)),
        }
    }

    fn from_coroutine_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        match kind {
            ClosureKind::Fn | ClosureKind::FnMut => Ty::new(TyKind::Int(IntTy::I16)),
            ClosureKind::FnOnce => Ty::new(TyKind::Int(IntTy::I32)),
        }
    }

    fn discriminant_ty(self, interner: DbInterner) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        match self.clone().kind() {
            TyKind::Adt(adt, _) if adt.is_enum() => adt.repr().discr_type().to_ty(interner),
            TyKind::Coroutine(_, args) => args.as_coroutine().discr_ty(interner),

            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Infer(InferTy::TyVar(_)) => {
                /*
                let assoc_items = tcx.associated_item_def_ids(
                    tcx.require_lang_item(hir::LangItem::DiscriminantKind, None),
                );
                TyKind::new_projection_from_args(tcx, assoc_items[0], tcx.mk_args(&[self.into()]))
                */
                todo!()
            }

            TyKind::Pat(ty, _) => ty.discriminant_ty(interner),

            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Adt(..)
            | TyKind::Foreign(_)
            | TyKind::Str
            | TyKind::Array(..)
            | TyKind::Slice(_)
            | TyKind::RawPtr(_, _)
            | TyKind::Ref(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(..)
            | TyKind::Dynamic(..)
            | TyKind::Closure(..)
            | TyKind::CoroutineClosure(..)
            | TyKind::CoroutineWitness(..)
            | TyKind::Never
            | TyKind::Tuple(_)
            | TyKind::Error(_)
            | TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => {
                Ty::new(TyKind::Uint(UintTy::U8))
            }

            TyKind::Bound(..)
            | TyKind::Placeholder(_)
            | TyKind::Infer(
                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_),
            ) => {
                panic!("`discriminant_ty` applied to unexpected type: {:?}", self)
            }
        }
    }

    fn async_destructor_ty(
        self,
        interner: DbInterner,
    ) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        // Very complicated
        Ty::new_unit(interner)
    }
}

impl Ty {
    /// Returns the `Size` for primitive types (bool, uint, int, char, float).
    pub fn primitive_size(self, interner: DbInterner) -> Size {
        match self.kind() {
            TyKind::Bool => Size::from_bytes(1),
            TyKind::Char => Size::from_bytes(4),
            TyKind::Int(ity) => Integer::from_int_ty(&interner, ity).size(),
            TyKind::Uint(uty) => Integer::from_uint_ty(&interner, uty).size(),
            TyKind::Float(fty) => Float::from_float_ty(fty).size(),
            _ => panic!("non primitive type"),
        }
    }

    pub fn int_size_and_signed(self, interner: DbInterner) -> (Size, bool) {
        match self.kind() {
            TyKind::Int(ity) => (Integer::from_int_ty(&interner, ity).size(), true),
            TyKind::Uint(uty) => (Integer::from_uint_ty(&interner, uty).size(), false),
            _ => panic!("non integer discriminant"),
        }
    }
}

impl ParamLike for ParamTy {
    fn index(&self) -> u32 {
        self.index
    }
}

impl BoundVarLike<DbInterner> for BoundTy {
    fn var(&self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_ty())
    }
}

impl PlaceholderLike for PlaceholderTy {
    fn universe(&self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(&self) -> BoundVar {
        self.bound.var
    }

    fn with_updated_universe(&self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound.clone() }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundTy { var, kind: BoundTyKind::Anon } }
    }
}
