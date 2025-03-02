//! This module contains code to instantiate new values into a
//! `Canonical<'tcx, T>`.
//!
//! For an overview of what canonicalization is and how it fits into
//! rustc, check out the [chapter in the rustc dev guide][c].
//!
//! [c]: https://rust-lang.github.io/chalk/book/canonical_queries/canonicalization.html

use crate::next_solver::{
    fold::FnMutDelegate,
    infer::{
        traits::{Obligation, PredicateObligations},
        DefineOpaqueTypes, InferCtxt, SubregionOrigin, TypeTrace,
    },
    AliasTy, Binder, BoundRegion, BoundTy, Canonical, CanonicalVarValues, Const, DbInterner, DbIr,
    Goal, ParamEnv, Predicate, PredicateKind, Region, Span, Ty, TyKind,
};
use extension_traits::extension;
use rustc_type_ir::{
    fold::TypeFoldable,
    inherent::{IntoKind, SliceLike},
    relate::{
        combine::{super_combine_consts, super_combine_tys},
        Relate, TypeRelation, VarianceDiagInfo,
    },
    AliasRelationDirection, AliasTyKind, BoundVar, GenericArgKind, InferTy, Upcast, Variance,
};

/// FIXME(-Znext-solver): This or public because it is shared with the
/// new trait solver implementation. We should deduplicate canonicalization.
#[extension(pub trait CanonicalExt)]
impl<V> Canonical<V> {
    /// Instantiate the wrapped value, replacing each canonical value
    /// with the value given in `var_values`.
    fn instantiate(&self, tcx: DbInterner, var_values: &CanonicalVarValues) -> V
    where
        V: TypeFoldable<DbInterner>,
    {
        self.instantiate_projected(tcx, var_values, |value| value.clone())
    }

    /// Allows one to apply a instantiation to some subset of
    /// `self.value`. Invoke `projection_fn` with `self.value` to get
    /// a value V that is expressed in terms of the same canonical
    /// variables bound in `self` (usually this extracts from subset
    /// of `self`). Apply the instantiation `var_values` to this value
    /// V, replacing each of the canonical variables.
    fn instantiate_projected<T>(
        &self,
        tcx: DbInterner,
        var_values: &CanonicalVarValues,
        projection_fn: impl FnOnce(&V) -> T,
    ) -> T
    where
        T: TypeFoldable<DbInterner>,
    {
        assert_eq!(self.variables.len(), var_values.len());
        let value = projection_fn(&self.value);
        instantiate_value(tcx, var_values, value)
    }
}

/// Instantiate the values from `var_values` into `value`. `var_values`
/// must be values for the set of canonical variables that appear in
/// `value`.
pub(super) fn instantiate_value<T>(tcx: DbInterner, var_values: &CanonicalVarValues, value: T) -> T
where
    T: TypeFoldable<DbInterner>,
{
    if var_values.var_values.clone().is_empty() {
        value
    } else {
        let delegate = FnMutDelegate {
            regions: &mut |br: BoundRegion| match var_values[br.var].clone().kind() {
                GenericArgKind::Lifetime(l) => l,
                r => panic!("{:?} is a region but value is {:?}", br, r),
            },
            types: &mut |bound_ty: BoundTy| match var_values[bound_ty.var].clone().kind() {
                GenericArgKind::Type(ty) => ty,
                r => panic!("{:?} is a type but value is {:?}", bound_ty, r),
            },
            consts: &mut |bound_ct: BoundVar| match var_values[bound_ct].clone().kind() {
                GenericArgKind::Const(ct) => ct,
                c => panic!("{:?} is a const but value is {:?}", bound_ct, c),
            },
        };

        tcx.replace_escaping_bound_vars_uncached(value, delegate)
    }
}
