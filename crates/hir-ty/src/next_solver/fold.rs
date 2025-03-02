use rustc_type_ir::{
    fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    inherent::{IntoKind, Region as _},
    visit::TypeVisitableExt,
    BoundVar, DebruijnIndex, RegionKind,
};

use super::{
    Binder, BoundRegion, BoundTy, Const, ConstKind, DbInterner, Predicate, Region, Ty, TyKind,
};

/// A delegate used when instantiating bound vars.
///
/// Any implementation must make sure that each bound variable always
/// gets mapped to the same result. `BoundVarReplacer` caches by using
/// a `DelayedMap` which does not cache the first few types it encounters.
pub trait BoundVarReplacerDelegate {
    fn replace_region(&mut self, br: BoundRegion) -> Region;
    fn replace_ty(&mut self, bt: BoundTy) -> Ty;
    fn replace_const(&mut self, bv: BoundVar) -> Const;
}

/// A simple delegate taking 3 mutable functions. The used functions must
/// always return the same result for each bound variable, no matter how
/// frequently they are called.
pub struct FnMutDelegate<'a> {
    pub regions: &'a mut (dyn FnMut(BoundRegion) -> Region + 'a),
    pub types: &'a mut (dyn FnMut(BoundTy) -> Ty + 'a),
    pub consts: &'a mut (dyn FnMut(BoundVar) -> Const + 'a),
}

impl BoundVarReplacerDelegate for FnMutDelegate<'_> {
    fn replace_region(&mut self, br: BoundRegion) -> Region {
        (self.regions)(br)
    }
    fn replace_ty(&mut self, bt: BoundTy) -> Ty {
        (self.types)(bt)
    }
    fn replace_const(&mut self, bv: BoundVar) -> Const {
        (self.consts)(bv)
    }
}

/// Replaces the escaping bound vars (late bound regions or bound types) in a type.
pub(crate) struct BoundVarReplacer<D> {
    /// As with `RegionFolder`, represents the index of a binder *just outside*
    /// the ones we have visited.
    current_index: DebruijnIndex,

    delegate: D,
}

impl<D: BoundVarReplacerDelegate> BoundVarReplacer<D> {
    pub fn new(tcx: DbInterner, delegate: D) -> Self {
        BoundVarReplacer { current_index: DebruijnIndex::ZERO, delegate }
    }
}

impl<D> TypeFolder<DbInterner> for BoundVarReplacer<D>
where
    D: BoundVarReplacerDelegate,
{
    fn cx(&self) -> DbInterner {
        DbInterner
    }

    fn fold_binder<T: TypeFoldable<DbInterner>>(&mut self, t: Binder<T>) -> Binder<T> {
        self.current_index.shift_in(1);
        let t = t.super_fold_with(self);
        self.current_index.shift_out(1);
        t
    }

    fn fold_ty(&mut self, t: Ty) -> Ty {
        match t.clone().kind() {
            TyKind::Bound(debruijn, bound_ty) if debruijn == self.current_index => {
                let ty = self.delegate.replace_ty(bound_ty);
                debug_assert!(!ty.has_vars_bound_above(DebruijnIndex::ZERO));
                rustc_type_ir::fold::shift_vars(DbInterner, ty, self.current_index.as_u32())
            }
            _ => {
                if !t.has_vars_bound_at_or_above(self.current_index) {
                    t
                } else {
                    t.super_fold_with(self)
                }
            }
        }
    }

    fn fold_region(&mut self, r: Region) -> Region {
        match r.clone().kind() {
            RegionKind::ReBound(debruijn, br) if debruijn == self.current_index => {
                let region = self.delegate.replace_region(br);
                if let RegionKind::ReBound(debruijn1, br) = region.clone().kind() {
                    // If the callback returns a bound region,
                    // that region should always use the INNERMOST
                    // debruijn index. Then we adjust it to the
                    // correct depth.
                    assert_eq!(debruijn1, DebruijnIndex::ZERO);
                    Region::new_bound(DbInterner, debruijn, br)
                } else {
                    region
                }
            }
            _ => r,
        }
    }

    fn fold_const(&mut self, ct: Const) -> Const {
        match ct.clone().kind() {
            ConstKind::Bound(debruijn, bound_const) if debruijn == self.current_index => {
                let ct = self.delegate.replace_const(bound_const);
                debug_assert!(!ct.has_vars_bound_above(DebruijnIndex::ZERO));
                rustc_type_ir::fold::shift_vars(DbInterner, ct, self.current_index.as_u32())
            }
            _ => ct.super_fold_with(self),
        }
    }

    fn fold_predicate(&mut self, p: Predicate) -> Predicate {
        if p.has_vars_bound_at_or_above(self.current_index) {
            p.super_fold_with(self)
        } else {
            p
        }
    }
}
