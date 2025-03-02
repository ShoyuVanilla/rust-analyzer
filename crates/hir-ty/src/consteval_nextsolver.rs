//! Constant evaluation details

use base_db::CrateId;
use hir_def::{
    expr_store::{Body, HygieneId},
    hir::{Expr, ExprId},
    path::Path,
    resolver::{Resolver, ValueNs},
    type_ref::LiteralConstRef,
    EnumVariantId,
};
use hir_expand::Lookup;
use rustc_type_ir::inherent::IntoKind;
use stdx::never;
use triomphe::Arc;

use crate::{
    consteval::ConstEvalError,
    db::HirDatabase,
    generics::Generics,
    infer::InferenceContext,
    layout_nextsolver::layout_of_ty_query,
    next_solver::{
        mapping::ChalkToNextSolver, Const, ConstKind, GenericArg, ParamConst, Ty, ValueConst,
    },
    ConstScalar, Interner, MemoryMap, Substitution, TraitEnvironment,
};

use super::mir::{interpret_mir, lower_to_mir, pad16};

pub(crate) fn path_to_const<'g>(
    db: &dyn HirDatabase,
    resolver: &Resolver,
    path: &Path,
    args: impl FnOnce() -> Option<&'g Generics>,
    expected_ty: Ty,
) -> Option<Const> {
    match resolver.resolve_path_in_value_ns_fully(db.upcast(), path, HygieneId::ROOT) {
        Some(ValueNs::GenericParam(p)) => {
            let args = args();
            match args
                .and_then(|args| args.type_or_const_param(p.into()))
                .and_then(|(idx, p)| p.const_param().map(|p| (idx, p)))
            {
                Some((idx, param)) => Some(Const::new_param(ParamConst {
                    index: idx as u32,
                    name: param.name.symbol().clone(),
                })),
                None => {
                    never!(
                        "Generic list doesn't contain this param: {:?}, {:?}, {:?}",
                        args,
                        path,
                        p
                    );
                    None
                }
            }
        }
        Some(ValueNs::ConstId(c)) => Some(intern_const_scalar(
            ConstScalar::UnevaluatedConst(c.into(), Substitution::empty(crate::Interner)),
            expected_ty,
        )),
        _ => None,
    }
}

pub fn unknown_const(ty: Ty) -> Const {
    Const::new(rustc_type_ir::ConstKind::Value(ty, ValueConst::new(ConstScalar::Unknown)))
}

pub fn unknown_const_as_generic(ty: Ty) -> GenericArg {
    unknown_const(ty).into()
}

/// Interns a constant scalar with the given type
pub fn intern_const_scalar(value: ConstScalar, ty: Ty) -> Const {
    Const::new(rustc_type_ir::ConstKind::Value(ty, ValueConst::new(value)))
}

/// Interns a constant scalar with the given type
pub fn intern_const_ref(
    db: &dyn HirDatabase,
    value: &LiteralConstRef,
    ty: Ty,
    krate: CrateId,
) -> Const {
    let layout = layout_of_ty_query(db, ty.clone(), TraitEnvironment::empty(krate));
    let bytes = match value {
        LiteralConstRef::Int(i) => {
            // FIXME: We should handle failure of layout better.
            let size = layout.map(|it| it.size.bytes_usize()).unwrap_or(16);
            ConstScalar::Bytes(i.to_le_bytes()[0..size].into(), MemoryMap::default())
        }
        LiteralConstRef::UInt(i) => {
            let size = layout.map(|it| it.size.bytes_usize()).unwrap_or(16);
            ConstScalar::Bytes(i.to_le_bytes()[0..size].into(), MemoryMap::default())
        }
        LiteralConstRef::Bool(b) => ConstScalar::Bytes(Box::new([*b as u8]), MemoryMap::default()),
        LiteralConstRef::Char(c) => {
            ConstScalar::Bytes((*c as u32).to_le_bytes().into(), MemoryMap::default())
        }
        LiteralConstRef::Unknown => ConstScalar::Unknown,
    };
    intern_const_scalar(bytes, ty)
}

/// Interns a possibly-unknown target usize
pub fn usize_const(db: &dyn HirDatabase, value: Option<u128>, krate: CrateId) -> Const {
    intern_const_ref(
        db,
        &value.map_or(LiteralConstRef::Unknown, LiteralConstRef::UInt),
        Ty::new_uint(rustc_type_ir::UintTy::Usize),
        krate,
    )
}

pub fn try_const_usize(db: &dyn HirDatabase, c: &Const) -> Option<u128> {
    match c.clone().kind() {
        ConstKind::Param(_) => None,
        ConstKind::Infer(_) => None,
        ConstKind::Bound(_, _) => None,
        ConstKind::Placeholder(_) => None,
        ConstKind::Unevaluated(_) => todo!(),
        ConstKind::Value(_, val) => match val.0 {
            ConstScalar::Bytes(it, _) => Some(u128::from_le_bytes(pad16(&it, false))),
            ConstScalar::UnevaluatedConst(c, subst) => {
                let fake_ir = crate::next_solver::DbIr::new(
                    db,
                    CrateId::from_raw(la_arena::RawIdx::from_u32(0)),
                    None,
                );
                let ec = db.const_eval(c, subst.clone(), None).ok()?.to_nextsolver(fake_ir);
                try_const_usize(db, &ec)
            }
            ConstScalar::Unknown => None,
        },
        ConstKind::Error(_) => None,
        ConstKind::Expr(_) => todo!(),
    }
}

pub fn try_const_isize(db: &dyn HirDatabase, c: &Const) -> Option<i128> {
    match c.clone().kind() {
        ConstKind::Param(_) => None,
        ConstKind::Infer(_) => None,
        ConstKind::Bound(_, _) => None,
        ConstKind::Placeholder(_) => None,
        ConstKind::Unevaluated(_) => todo!(),
        ConstKind::Value(_, val) => match val.0 {
            ConstScalar::Bytes(it, _) => Some(i128::from_le_bytes(pad16(&it, false))),
            ConstScalar::UnevaluatedConst(c, subst) => {
                let fake_ir = crate::next_solver::DbIr::new(
                    db,
                    CrateId::from_raw(la_arena::RawIdx::from_u32(0)),
                    None,
                );
                let ec = db.const_eval(c, subst.clone(), None).ok()?.to_nextsolver(fake_ir);
                try_const_isize(db, &ec)
            }
            ConstScalar::Unknown => None,
        },
        ConstKind::Error(_) => None,
        ConstKind::Expr(_) => todo!(),
    }
}

pub(crate) fn const_eval_discriminant_variant(
    db: &dyn HirDatabase,
    variant_id: EnumVariantId,
) -> Result<i128, ConstEvalError> {
    let fake_ir =
        crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let def = variant_id.into();
    let body = db.body(def);
    let loc = variant_id.lookup(db.upcast());
    if body.exprs[body.body_expr] == Expr::Missing {
        let prev_idx = loc.index.checked_sub(1);
        let value = match prev_idx {
            Some(prev_idx) => {
                1 + db.const_eval_discriminant(
                    db.enum_data(loc.parent).variants[prev_idx as usize].0,
                )?
            }
            _ => 0,
        };
        return Ok(value);
    }

    let repr = db.enum_data(loc.parent).repr;
    let is_signed = repr.and_then(|repr| repr.int).is_none_or(|int| int.is_signed());

    let mir_body = db.monomorphized_mir_body(
        def,
        Substitution::empty(Interner),
        db.trait_environment_for_body(def),
    )?;
    let c = interpret_mir(db, mir_body, false, None)?.0?;
    let c = c.to_nextsolver(fake_ir);
    let c = if is_signed {
        try_const_isize(db, &c).unwrap()
    } else {
        try_const_usize(db, &c).unwrap() as i128
    };
    Ok(c)
}

// FIXME: Ideally constants in const eval should have separate body (issue #7434), and this function should
// get an `InferenceResult` instead of an `InferenceContext`. And we should remove `ctx.clone().resolve_all()` here
// and make this function private. See the fixme comment on `InferenceContext::resolve_all`.
pub(crate) fn eval_to_const(expr: ExprId, ctx: &mut InferenceContext<'_>) -> Const {
    let db = ctx.db;
    let fake_ir =
        crate::next_solver::DbIr::new(db, CrateId::from_raw(la_arena::RawIdx::from_u32(0)), None);
    let infer = ctx.clone().resolve_all();
    fn has_closure(body: &Body, expr: ExprId) -> bool {
        if matches!(body[expr], Expr::Closure { .. }) {
            return true;
        }
        let mut r = false;
        body.walk_child_exprs(expr, |idx| r |= has_closure(body, idx));
        r
    }
    if has_closure(ctx.body, expr) {
        // Type checking clousres need an isolated body (See the above FIXME). Bail out early to prevent panic.
        return unknown_const(infer[expr].clone().to_nextsolver(fake_ir));
    }
    if let Expr::Path(p) = &ctx.body.exprs[expr] {
        let resolver = &ctx.resolver;
        if let Some(c) =
            path_to_const(db, resolver, p, || ctx.generics(), infer[expr].to_nextsolver(fake_ir))
        {
            return c;
        }
    }
    if let Ok(mir_body) = lower_to_mir(ctx.db, ctx.owner, ctx.body, &infer, expr) {
        if let Ok((Ok(result), _)) = interpret_mir(db, Arc::new(mir_body), true, None) {
            return result.to_nextsolver(fake_ir);
        }
    }
    unknown_const(infer[expr].to_nextsolver(fake_ir))
}
