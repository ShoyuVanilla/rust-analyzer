//! Helper routines for higher-ranked things. See the `doc` module at
//! the end of the file for details.

use rustc_type_ir::fold::TypeFoldable;
use rustc_type_ir::{BoundVar, UniverseIndex};
use tracing::{debug, instrument};

use super::RelateResult;
use crate::next_solver::fold::FnMutDelegate;
use crate::next_solver::infer::InferCtxt;
use crate::next_solver::infer::snapshot::CombinedSnapshot;
use crate::next_solver::{Binder, BoundRegion, BoundTy, Const, DbInterner, PlaceholderConst, PlaceholderRegion, PlaceholderTy, Region, Ty};

impl<'db> InferCtxt<'db> {
    /// Replaces all bound variables (lifetimes, types, and constants) bound by
    /// `binder` with placeholder variables in a new universe. This means that the
    /// new placeholders can only be named by inference variables created after
    /// this method has been called.
    ///
    /// This is the first step of checking subtyping when higher-ranked things are involved.
    /// For more details visit the relevant sections of the [rustc dev guide].
    ///
    /// `fn enter_forall` should be preferred over this method.
    ///
    /// [rustc dev guide]: https://rustc-dev-guide.rust-lang.org/traits/hrtb.html
    #[instrument(level = "debug", skip(self), ret)]
    pub fn enter_forall_and_leak_universe<T>(&self, binder: Binder<T>) -> T
    where
        T: TypeFoldable<DbInterner> + Clone,
    {
        if let Some(inner) = binder.clone().no_bound_vars() {
            return inner;
        }

        let next_universe = self.create_next_universe();

        let delegate = FnMutDelegate {
            regions: &mut |br: BoundRegion| {
                Region::new_placeholder(PlaceholderRegion {
                    universe: next_universe,
                    bound: br,
                })
            },
            types: &mut |bound_ty: BoundTy| {
                Ty::new_placeholder(PlaceholderTy {
                    universe: next_universe,
                    bound: bound_ty,
                })
            },
            consts: &mut |bound_var: BoundVar| {
                Const::new_placeholder(PlaceholderConst {
                    universe: next_universe,
                    bound: bound_var,
                })
            },
        };

        debug!(?next_universe);
        DbInterner.replace_bound_vars_uncached(binder, delegate)
    }

    /// Replaces all bound variables (lifetimes, types, and constants) bound by
    /// `binder` with placeholder variables in a new universe and then calls the
    /// closure `f` with the instantiated value. The new placeholders can only be
    /// named by inference variables created inside of the closure `f` or afterwards.
    ///
    /// This is the first step of checking subtyping when higher-ranked things are involved.
    /// For more details visit the relevant sections of the [rustc dev guide].
    ///
    /// This method should be preferred over `fn enter_forall_and_leak_universe`.
    ///
    /// [rustc dev guide]: https://rustc-dev-guide.rust-lang.org/traits/hrtb.html
    #[instrument(level = "debug", skip(self, f))]
    pub fn enter_forall<T, U>(&self, forall: Binder<T>, f: impl FnOnce(T) -> U) -> U
    where
        T: TypeFoldable<DbInterner> + Clone,
    {
        // FIXME: currently we do nothing to prevent placeholders with the new universe being
        // used after exiting `f`. For example region subtyping can result in outlives constraints
        // that name placeholders created in this function. Nested goals from type relations can
        // also contain placeholders created by this function.
        let value = self.enter_forall_and_leak_universe(forall);
        debug!(?value);
        f(value)
    }

    /// See [RegionConstraintCollector::leak_check][1]. We only check placeholder
    /// leaking into `outer_universe`, i.e. placeholders which cannot be named by that
    /// universe.
    ///
    /// [1]: crate::infer::region_constraints::RegionConstraintCollector::leak_check
    pub fn leak_check(
        &self,
        outer_universe: UniverseIndex,
        only_consider_snapshot: Option<&CombinedSnapshot>,
    ) -> RelateResult<()> {
        Ok(())
    }
}
