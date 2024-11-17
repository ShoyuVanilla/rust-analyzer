use hir_def::GenericDefId;
use intern::Interned;
use rustc_ast_ir::{try_visit, visit::VisitorResult};
use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{BoundVarLike, IntoKind, ParamLike, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    BoundVar, TyKind,
};
use smallvec::SmallVec;

use crate::interner::InternedWrapper;

use super::{BoundVarKind, DbInterner, GenericArgs, Placeholder, Symbol};

pub type FnHeader = rustc_type_ir::FnHeader<DbInterner>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ty(Interned<InternedWrapper<TyKind<DbInterner>>>);

impl Ty {
    pub fn new(kind: TyKind<DbInterner>) -> Self {
        Ty(Interned::new(InternedWrapper(kind)))
    }
}

type InternedTys = Interned<InternedWrapper<SmallVec<[Ty; 2]>>>;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Tys(InternedTys);

impl Tys {
    pub fn new(data: impl IntoIterator<Item = Ty>) -> Self {
        Tys(Interned::new(InternedWrapper(data.into_iter().collect())))
    }
}

impl Default for Tys {
    fn default() -> Self {
        todo!()
    }
}

impl rustc_type_ir::fold::TypeFoldable<DbInterner> for Tys {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        _folder: &mut F,
    ) -> Result<Self, F::Error> {
        todo!()
    }
}

impl rustc_type_ir::visit::TypeVisitable<DbInterner> for Tys {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        _visitor: &mut V,
    ) -> V::Result {
        todo!()
    }
}

pub struct TysIter;
impl Iterator for TysIter {
    type Item = Ty;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl rustc_type_ir::inherent::SliceLike for Tys {
    type Item = Ty;
    type IntoIter = TysIter;

    fn iter(self) -> Self::IntoIter {
        todo!()
    }

    fn as_slice(&self) -> &[Self::Item] {
        todo!()
    }
}

impl rustc_type_ir::inherent::Tys<DbInterner> for Tys {
    fn inputs(self) -> <DbInterner as rustc_type_ir::Interner>::FnInputTys {
        todo!()
    }

    fn output(self) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }
}

pub type PlaceholderTy = Placeholder<BoundTy>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)] // FIXME implement Debug by hand
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug by hand
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BoundTyKind {
    Anon,
    Param(GenericDefId, Symbol),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ErrorGuaranteed;

impl Ty {
    pub fn error() -> Self {
        Ty::new(TyKind::Error(ErrorGuaranteed))
    }
}

impl IntoKind for Ty {
    type Kind = TyKind<DbInterner>;

    fn kind(self) -> Self::Kind {
        self.0 .0.clone()
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
            //TyKind::FnPtr(ref sig_tys, _) => sig_tys.visit_with(visitor),
            TyKind::FnPtr(ref sig_tys, _) => todo!(),
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
        todo!()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        todo!()
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
        Ty::new(TyKind::Tuple(Tys::new(tys.iter().cloned())))
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
        todo!()
    }

    fn from_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        todo!()
    }

    fn from_coroutine_closure_kind(interner: DbInterner, kind: rustc_type_ir::ClosureKind) -> Self {
        todo!()
    }

    fn discriminant_ty(self, interner: DbInterner) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }

    fn async_destructor_ty(
        self,
        interner: DbInterner,
    ) -> <DbInterner as rustc_type_ir::Interner>::Ty {
        todo!()
    }
}

impl ParamLike for ParamTy {
    fn index(&self) -> u32 {
        self.index
    }
}

impl BoundVarLike<DbInterner> for BoundTy {
    fn var(self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_ty())
    }
}

impl PlaceholderLike for PlaceholderTy {
    fn universe(self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(self) -> BoundVar {
        self.bound.var
    }

    fn with_updated_universe(self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, ..self }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundTy { var, kind: BoundTyKind::Anon } }
    }
}
