//! A nice interface for working with the infcx. The basic idea is to
//! do `infcx.at(cause, param_env)`, which sets the "cause" of the
//! operation as well as the surrounding parameter environment. Then
//! you can do something like `.sub(a, b)` or `.eq(a, b)` to create a
//! subtype or equality relationship respectively. The first argument
//! is always the "expected" output from the POV of diagnostics.
//!
//! Examples:
//! ```ignore (fragment)
//!     infcx.at(cause, param_env).sub(a, b)
//!     // requires that `a <: b`, with `a` considered the "expected" type
//!
//!     infcx.at(cause, param_env).sup(a, b)
//!     // requires that `b <: a`, with `a` considered the "expected" type
//!
//!     infcx.at(cause, param_env).eq(a, b)
//!     // requires that `a == b`, with `a` considered the "expected" type
//! ```
//! For finer-grained control, you can also do use `trace`:
//! ```ignore (fragment)
//!     infcx.at(...).trace(a, b).sub(&c, &d)
//! ```
//! This will set `a` and `b` as the "root" values for
//! error-reporting, but actually operate on `c` and `d`. This is
//! sometimes useful when the types of `c` and `d` are not traceable
//! things. (That system should probably be refactored.)

use rustc_type_ir::{
    error::ExpectedFound,
    inherent::IntoKind,
    relate::{solver_relating::RelateExt, Relate, TypeRelation},
    FnSig, GenericArgKind, TypingMode, Variance,
};

use crate::next_solver::{
    AliasTerm, AliasTy, Binder, Const, DbInterner, GenericArg, Goal, ParamEnv,
    PolyExistentialProjection, PolyExistentialTraitRef, PolyFnSig, Predicate, Region, Term,
    TraitRef, Ty,
};

use super::{
    relate::lattice::{LatticeOp, LatticeOpKind},
    traits::{Obligation, ObligationCause},
    InferCtxt, InferOk, InferResult, TypeTrace, ValuePairs,
};

/// Whether we should define opaque types or just treat them opaquely.
///
/// Currently only used to prevent predicate matching from matching anything
/// against opaque types.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DefineOpaqueTypes {
    Yes,
    No,
}

#[derive(Clone)]
pub struct At<'a, 'db> {
    pub infcx: &'a InferCtxt<'db>,
    pub cause: &'a ObligationCause,
    pub param_env: ParamEnv,
}

impl<'db> InferCtxt<'db> {
    #[inline]
    pub fn at<'a>(&'a self, cause: &'a ObligationCause, param_env: ParamEnv) -> At<'a, 'db> {
        At { infcx: self, cause, param_env }
    }

    /// Forks the inference context, creating a new inference context with the same inference
    /// variables in the same state. This can be used to "branch off" many tests from the same
    /// common state.
    pub fn fork(&self) -> Self {
        Self {
            ir: self.ir,
            typing_mode: self.typing_mode.clone(),
            considering_regions: self.considering_regions,
            skip_leak_check: self.skip_leak_check,
            inner: self.inner.clone(),
            reported_trait_errors: self.reported_trait_errors.clone(),
            reported_signature_mismatch: self.reported_signature_mismatch.clone(),
            tainted_by_errors: self.tainted_by_errors.clone(),
            universe: self.universe.clone(),
            obligation_inspector: self.obligation_inspector.clone(),
        }
    }

    /// Forks the inference context, creating a new inference context with the same inference
    /// variables in the same state, except possibly changing the intercrate mode. This can be
    /// used to "branch off" many tests from the same common state. Used in negative coherence.
    pub fn fork_with_typing_mode(&self, typing_mode: TypingMode<DbInterner>) -> Self {
        // Unlike `fork`, this invalidates all cache entries as they may depend on the
        // typing mode.

        Self {
            ir: self.ir,
            typing_mode,
            considering_regions: self.considering_regions,
            skip_leak_check: self.skip_leak_check,
            inner: self.inner.clone(),
            reported_trait_errors: self.reported_trait_errors.clone(),
            reported_signature_mismatch: self.reported_signature_mismatch.clone(),
            tainted_by_errors: self.tainted_by_errors.clone(),
            universe: self.universe.clone(),
            obligation_inspector: self.obligation_inspector.clone(),
        }
    }
}

pub trait ToTrace: Relate<DbInterner> {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace;
}

impl At<'_, '_> {
    /// Makes `actual <: expected`. For example, if type-checking a
    /// call like `foo(x)`, where `foo: fn(i32)`, you might have
    /// `sup(i32, x)`, since the "expected" type is the type that
    /// appears in the signature.
    pub fn sup<T>(
        self,
        define_opaque_types: DefineOpaqueTypes,
        expected: T,
        actual: T,
    ) -> InferResult<()>
    where
        T: ToTrace,
    {
        RelateExt::relate(
            self.infcx,
            self.param_env.clone(),
            expected,
            Variance::Contravariant,
            actual,
        )
        .map(|goals| self.goals_to_obligations(goals))
    }

    /// Makes `expected <: actual`.
    pub fn sub<T>(
        self,
        define_opaque_types: DefineOpaqueTypes,
        expected: T,
        actual: T,
    ) -> InferResult<()>
    where
        T: ToTrace,
    {
        RelateExt::relate(self.infcx, self.param_env.clone(), expected, Variance::Covariant, actual)
            .map(|goals| self.goals_to_obligations(goals))
    }

    /// Makes `expected == actual`.
    pub fn eq<T>(
        self,
        define_opaque_types: DefineOpaqueTypes,
        expected: T,
        actual: T,
    ) -> InferResult<()>
    where
        T: ToTrace,
    {
        self.clone().eq_trace(
            define_opaque_types,
            ToTrace::to_trace(self.cause, expected.clone(), actual.clone()),
            expected,
            actual,
        )
    }

    /// Makes `expected == actual`.
    pub fn eq_trace<T>(
        self,
        define_opaque_types: DefineOpaqueTypes,
        trace: TypeTrace,
        expected: T,
        actual: T,
    ) -> InferResult<()>
    where
        T: Relate<DbInterner>,
    {
        RelateExt::relate(self.infcx, self.param_env.clone(), expected, Variance::Invariant, actual)
            .map(|goals| self.goals_to_obligations(goals))
    }

    pub fn relate<T>(
        self,
        define_opaque_types: DefineOpaqueTypes,
        expected: T,
        variance: Variance,
        actual: T,
    ) -> InferResult<()>
    where
        T: ToTrace,
    {
        match variance {
            Variance::Covariant => self.sub(define_opaque_types, expected, actual),
            Variance::Invariant => self.eq(define_opaque_types, expected, actual),
            Variance::Contravariant => self.sup(define_opaque_types, expected, actual),

            // We could make this make sense but it's not readily
            // exposed and I don't feel like dealing with it. Note
            // that bivariance in general does a bit more than just
            // *nothing*, it checks that the types are the same
            // "modulo variance" basically.
            Variance::Bivariant => panic!("Bivariant given to `relate()`"),
        }
    }

    /// Computes the least-upper-bound, or mutual supertype, of two
    /// values. The order of the arguments doesn't matter, but since
    /// this can result in an error (e.g., if asked to compute LUB of
    /// u32 and i32), it is meaningful to call one of them the
    /// "expected type".
    pub fn lub<T>(self, expected: T, actual: T) -> InferResult<T>
    where
        T: ToTrace,
    {
        let mut op = LatticeOp::new(
            self.infcx,
            ToTrace::to_trace(self.cause, expected.clone(), actual.clone()),
            self.param_env,
            LatticeOpKind::Lub,
        );
        let value = op.relate(expected, actual)?;
        Ok(InferOk { value, obligations: op.into_obligations() })
    }

    fn goals_to_obligations(&self, goals: Vec<Goal<Predicate>>) -> InferOk<()> {
        InferOk {
            value: (),
            obligations: goals
                .into_iter()
                .map(|goal| {
                    Obligation::new(DbInterner, self.cause.clone(), goal.param_env, goal.predicate)
                })
                .collect(),
        }
    }
}

/*
impl ToTrace for ImplSubject {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        match (a, b) {
            (ImplSubject::Trait(trait_ref_a), ImplSubject::Trait(trait_ref_b)) => {
                ToTrace::to_trace(cause, trait_ref_a, trait_ref_b)
            }
            (ImplSubject::Inherent(ty_a), ImplSubject::Inherent(ty_b)) => {
                ToTrace::to_trace(cause, ty_a, ty_b)
            }
            (ImplSubject::Trait(_), ImplSubject::Inherent(_))
            | (ImplSubject::Inherent(_), ImplSubject::Trait(_)) => {
                panic!("can not trace TraitRef and Ty");
            }
        }
    }
}
*/

impl ToTrace for Ty {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Terms(ExpectedFound::new(true, a.into(), b.into())),
        }
    }
}

impl ToTrace for Region {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Regions(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for Const {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Terms(ExpectedFound::new(true, a.into(), b.into())),
        }
    }
}

impl ToTrace for GenericArg {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: match (a.clone().kind(), b.clone().kind()) {
                (GenericArgKind::Lifetime(a), GenericArgKind::Lifetime(b)) => {
                    ValuePairs::Regions(ExpectedFound::new(true, a, b))
                }
                (GenericArgKind::Type(a), GenericArgKind::Type(b)) => {
                    ValuePairs::Terms(ExpectedFound::new(true, a.into(), b.into()))
                }
                (GenericArgKind::Const(a), GenericArgKind::Const(b)) => {
                    ValuePairs::Terms(ExpectedFound::new(true, a.into(), b.into()))
                }
                _ => panic!("relating different kinds: {a:?} {b:?}"),
            },
        }
    }
}

impl ToTrace for Term {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Terms(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for TraitRef {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::TraitRefs(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for AliasTy {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Aliases(ExpectedFound::new(true, a.into(), b.into())),
        }
    }
}

impl ToTrace for AliasTerm {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Aliases(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for FnSig<DbInterner> {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::PolySigs(ExpectedFound::new(
                true,
                Binder::dummy(a),
                Binder::dummy(b),
            )),
        }
    }
}

impl ToTrace for PolyFnSig {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::PolySigs(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for PolyExistentialTraitRef {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::ExistentialTraitRef(ExpectedFound::new(true, a, b)),
        }
    }
}

impl ToTrace for PolyExistentialProjection {
    fn to_trace(cause: &ObligationCause, a: Self, b: Self) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::ExistentialProjection(ExpectedFound::new(true, a, b)),
        }
    }
}
