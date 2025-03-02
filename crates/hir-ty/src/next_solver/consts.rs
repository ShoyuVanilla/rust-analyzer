use intern::{Interned, Symbol};
use rustc_ast_ir::try_visit;
use rustc_ast_ir::visit::VisitorResult;
use rustc_type_ir::{
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{IntoKind, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    BoundVar, WithCachedTypeInfo,
};

use crate::{interner::InternedWrapper, ConstScalar};

use super::{
    flags::FlagComputation, BoundVarKind, DbInterner, ErrorGuaranteed, GenericArgs, Placeholder,
};

pub type ConstKind = rustc_type_ir::ConstKind<DbInterner>;
pub type UnevaluatedConst = rustc_type_ir::UnevaluatedConst<DbInterner>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Const(Interned<InternedWrapper<WithCachedTypeInfo<ConstKind>>>);

impl Const {
    pub fn new(kind: ConstKind) -> Self {
        let flags = FlagComputation::for_const_kind(&kind);
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Const(Interned::new(InternedWrapper(cached)))
    }

    pub fn error() -> Self {
        Const::new(rustc_type_ir::ConstKind::Error(ErrorGuaranteed))
    }

    pub fn new_param(param: ParamConst) -> Self {
        Const::new(rustc_type_ir::ConstKind::Param(param))
    }

    pub fn new_placeholder(placeholder: PlaceholderConst) -> Self {
        Const::new(ConstKind::Placeholder(placeholder))
    }

    pub fn is_ct_infer(&self) -> bool {
        matches!(&self.0.internee, ConstKind::Infer(_))
    }
}

impl std::fmt::Debug for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0 .0.internee.fmt(f)
    }
}

pub type PlaceholderConst = Placeholder<rustc_type_ir::BoundVar>;

#[derive(Clone, Hash, Eq, PartialEq, Debug)] // FIXME implement manually
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ValueConst(pub(crate) ConstScalar);

impl ValueConst {
    pub fn new(scalar: ConstScalar) -> Self {
        ValueConst(scalar)
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct ExprConst;

impl rustc_type_ir::inherent::ParamLike for ParamConst {
    fn index(&self) -> u32 {
        self.index
    }
}

impl IntoKind for Const {
    type Kind = ConstKind;

    fn kind(self) -> Self::Kind {
        self.0 .0.internee.clone()
    }
}

impl TypeVisitable<DbInterner> for Const {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_const(self.clone())
    }
}

impl TypeSuperVisitable<DbInterner> for Const {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        match self.clone().kind() {
            ConstKind::Param(p) => p.visit_with(visitor),
            //ConstKind::Infer(i) => i.visit_with(visitor),
            ConstKind::Infer(i) => V::Result::output(),
            ConstKind::Bound(d, b) => {
                try_visit!(d.visit_with(visitor));
                b.visit_with(visitor)
            }
            ConstKind::Placeholder(p) => p.visit_with(visitor),
            ConstKind::Unevaluated(uv) => uv.visit_with(visitor),
            ConstKind::Value(t, v) => {
                try_visit!(t.visit_with(visitor));
                v.visit_with(visitor)
            }
            //ConstKind::Error(e) => e.visit_with(visitor),
            ConstKind::Error(e) => V::Result::output(),
            ConstKind::Expr(e) => e.visit_with(visitor),
        }
    }
}

impl TypeFoldable<DbInterner> for Const {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_const(self)
    }
}

impl TypeSuperFoldable<DbInterner> for Const {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let kind = match self.clone().kind() {
            ConstKind::Param(p) => ConstKind::Param(p.try_fold_with(folder)?),
            //ConstKind::Infer(i) => ConstKind::Infer(i.try_fold_with(folder)?),
            ConstKind::Infer(i) => ConstKind::Infer(i),
            ConstKind::Bound(d, b) => {
                ConstKind::Bound(d.try_fold_with(folder)?, b.try_fold_with(folder)?)
            }
            ConstKind::Placeholder(p) => ConstKind::Placeholder(p.try_fold_with(folder)?),
            ConstKind::Unevaluated(uv) => ConstKind::Unevaluated(uv.try_fold_with(folder)?),
            ConstKind::Value(t, v) => {
                ConstKind::Value(t.try_fold_with(folder)?, v.try_fold_with(folder)?)
            }
            //ConstKind::Error(e) => ConstKind::Error(e.try_fold_with(folder)?),
            ConstKind::Error(e) => ConstKind::Error(e),
            ConstKind::Expr(e) => ConstKind::Expr(e.try_fold_with(folder)?),
        };
        if kind != self.clone().kind() {
            Ok(Const::new(kind))
        } else {
            Ok(self)
        }
    }
}

impl Relate<DbInterner> for Const {
    fn relate<R: rustc_type_ir::relate::TypeRelation<I = DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        relation.consts(a, b)
    }
}

impl Flags for Const {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.0.flags
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.0.outer_exclusive_binder
    }
}

impl rustc_type_ir::inherent::Const<DbInterner> for Const {
    fn try_to_target_usize(self, interner: DbInterner) -> Option<u64> {
        todo!()
    }

    fn new_infer(interner: DbInterner, var: rustc_type_ir::InferConst) -> Self {
        Const::new(ConstKind::Infer(var))
    }

    fn new_var(interner: DbInterner, var: rustc_type_ir::ConstVid) -> Self {
        Const::new(ConstKind::Infer(rustc_type_ir::InferConst::Var(var)))
    }

    fn new_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundVar,
    ) -> Self {
        Const::new(ConstKind::Bound(debruijn, var))
    }

    fn new_anon_bound(
        interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        Const::new(ConstKind::Bound(debruijn, var))
    }

    fn new_unevaluated(
        interner: DbInterner,
        uv: rustc_type_ir::UnevaluatedConst<DbInterner>,
    ) -> Self {
        Const::new(ConstKind::Unevaluated(uv))
    }

    fn new_expr(interner: DbInterner, expr: ExprConst) -> Self {
        Const::new(ConstKind::Expr(expr))
    }

    fn new_error(interner: DbInterner, guar: ErrorGuaranteed) -> Self {
        Const::new(ConstKind::Error(guar))
    }
}

impl PlaceholderLike for PlaceholderConst {
    fn universe(&self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(&self) -> rustc_type_ir::BoundVar {
        self.bound
    }

    fn with_updated_universe(&self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: var }
    }
}

impl TypeVisitable<DbInterner> for ExprConst {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = &self;
        V::Result::output()
    }
}

impl TypeFoldable<DbInterner> for ExprConst {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(ExprConst)
    }
}

impl Relate<DbInterner> for ExprConst {
    fn relate<R: rustc_type_ir::relate::TypeRelation>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = b;
        Ok(a)
    }
}

impl rustc_type_ir::inherent::ExprConst<DbInterner> for ExprConst {
    fn args(self) -> <DbInterner as rustc_type_ir::Interner>::GenericArgs {
        // Ensure we get back to this when we fill in the fields
        let ExprConst = self;
        GenericArgs::default()
    }
}
