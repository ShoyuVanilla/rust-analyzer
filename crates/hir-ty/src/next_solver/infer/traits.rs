//! Trait Resolution. See the [rustc-dev-guide] for more information on how this works.
//!
//! [rustc-dev-guide]: https://rustc-dev-guide.rust-lang.org/traits/resolution.html

use std::{cmp, hash::{Hash, Hasher}};

use hir_def::GenericDefId;
use rustc_type_ir::{solve::{Certainty, NoSolution}, PredicatePolarity, Upcast};
use stdx::thin_vec::ThinVec;

use crate::next_solver::{Binder, DbInterner, Goal, ParamEnv, PolyTraitPredicate, Predicate, Span, TraitPredicate, Ty};

use super::InferCtxt;

/// The reason why we incurred this obligation; used for error reporting.
///
/// Non-misc `ObligationCauseCode`s are stored on the heap. This gives the
/// best trade-off between keeping the type small (which makes copies cheaper)
/// while not doing too many heap allocations.
///
/// We do not want to intern this as there are a lot of obligation causes which
/// only live for a short period of time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObligationCause {
    pub span: Span,

    /// The ID of the fn body that triggered this obligation. This is
    /// used for region obligations to determine the precise
    /// environment in which the region obligation should be evaluated
    /// (in particular, closures can add new assumptions). See the
    /// field `region_obligations` of the `FulfillmentContext` for more
    /// information.
    pub body_id: Option<GenericDefId>,
}


impl ObligationCause {
    #[inline]
    pub fn new(
        span: Span,
        body_id: GenericDefId,
    ) -> ObligationCause {
        ObligationCause { span, body_id: Some(body_id) }
    }

    #[inline(always)]
    pub fn dummy_with_span(span: Span) -> ObligationCause {
        ObligationCause { span, body_id: None }
    }
}

/// An `Obligation` represents some trait reference (e.g., `i32: Eq`) for
/// which the "impl_source" must be found. The process of finding an "impl_source" is
/// called "resolving" the `Obligation`. This process consists of
/// either identifying an `impl` (e.g., `impl Eq for i32`) that
/// satisfies the obligation, or else finding a bound that is in
/// scope. The eventual result is usually a `Selection` (defined below).
#[derive(Clone, Debug)]
pub struct Obligation<T> {
    /// The reason we have to prove this thing.
    pub cause: ObligationCause,

    /// The environment in which we should prove this thing.
    pub param_env: ParamEnv,

    /// The thing we are trying to prove.
    pub predicate: T,

    /// If we started proving this as a result of trying to prove
    /// something else, track the total depth to ensure termination.
    /// If this goes over a certain threshold, we abort compilation --
    /// in such cases, we can not say whether or not the predicate
    /// holds for certain. Stupid halting problem; such a drag.
    pub recursion_depth: usize,
}

impl<T: PartialEq> PartialEq<Obligation<T>> for Obligation<T> {
    #[inline]
    fn eq(&self, other: &Obligation<T>) -> bool {
        // Ignore `cause` and `recursion_depth`. This is a small performance
        // win for a few crates, and a huge performance win for the crate in
        // https://github.com/rust-lang/rustc-perf/pull/1680, which greatly
        // stresses the trait system.
        self.param_env == other.param_env && self.predicate == other.predicate
    }
}

impl<T: Eq> Eq for Obligation<T> {}

impl<T: Hash> Hash for Obligation<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // See the comment on `Obligation::eq`.
        self.param_env.hash(state);
        self.predicate.hash(state);
    }
}

impl<P> From<Obligation<P>> for Goal<P> {
    fn from(value: Obligation<P>) -> Self {
        Goal { param_env: value.param_env, predicate: value.predicate }
    }
}

pub type PredicateObligation = Obligation<Predicate>;
pub type TraitObligation = Obligation<TraitPredicate>;
pub type PolyTraitObligation = Obligation<PolyTraitPredicate>;

pub type PredicateObligations = Vec<PredicateObligation>;

impl PredicateObligation {
    /// Flips the polarity of the inner predicate.
    ///
    /// Given `T: Trait` predicate it returns `T: !Trait` and given `T: !Trait` returns `T: Trait`.
    pub fn flip_polarity(&self, tcx: DbInterner) -> Option<PredicateObligation> {
        Some(PredicateObligation {
            cause: self.cause.clone(),
            param_env: self.param_env.clone(),
            predicate: self.predicate.clone().flip_polarity()?,
            recursion_depth: self.recursion_depth,
        })
    }
}

/// A callback that can be provided to `inspect_typeck`. Invoked on evaluation
/// of root obligations.
pub type ObligationInspector<'db> =
    fn(&InferCtxt<'db>, &PredicateObligation, Result<Certainty, NoSolution>);

impl<O> Obligation<O> {
    pub fn new(
        tcx: DbInterner,
        cause: ObligationCause,
        param_env: ParamEnv,
        predicate: impl Upcast<DbInterner, O>,
    ) -> Obligation<O> {
        Self::with_depth(tcx, cause, 0, param_env, predicate)
    }

    /// We often create nested obligations without setting the correct depth.
    ///
    /// To deal with this evaluate and fulfill explicitly update the depth
    /// of nested obligations using this function.
    pub fn set_depth_from_parent(&mut self, parent_depth: usize) {
        self.recursion_depth = cmp::max(parent_depth + 1, self.recursion_depth);
    }

    pub fn with_depth(
        tcx: DbInterner,
        cause: ObligationCause,
        recursion_depth: usize,
        param_env: ParamEnv,
        predicate: impl Upcast<DbInterner, O>,
    ) -> Obligation<O> {
        let predicate = predicate.upcast(tcx);
        Obligation { cause, param_env, recursion_depth, predicate }
    }

    pub fn misc(
        tcx: DbInterner,
        span: Span,
        body_id: GenericDefId,
        param_env: ParamEnv,
        trait_ref: impl Upcast<DbInterner, O>,
    ) -> Obligation<O> {
        Obligation::new(tcx, ObligationCause::new(span, body_id), param_env, trait_ref)
    }

    pub fn with<P>(
        &self,
        tcx: DbInterner,
        value: impl Upcast<DbInterner, P>,
    ) -> Obligation<P> {
        Obligation::with_depth(tcx, self.cause.clone(), self.recursion_depth, self.param_env.clone(), value)
    }
}

impl PolyTraitObligation {
    pub fn polarity(&self) -> PredicatePolarity {
        self.predicate.clone().skip_binder().polarity
    }

    pub fn self_ty(&self) -> Binder<Ty> {
        self.predicate.clone().map_bound(|p| p.self_ty())
    }
}
