use std::cell::{Cell, RefCell};
use std::fmt;
use std::sync::Arc;

use ena::undo_log::UndoLogs;
use extension_traits::extension;
use hir_def::GenericDefId;
use intern::Symbol;
use project::ProjectionCacheStorage;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_pattern_analysis::Captures;
use rustc_type_ir::error::{ExpectedFound, TypeError};
use rustc_type_ir::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use rustc_type_ir::inherent::{Const as _, GenericArg as _, GenericArgs as _, IntoKind, ParamEnv as _, SliceLike, Term as _, Ty as _};
use rustc_type_ir::visit::TypeVisitableExt;
use rustc_type_ir::{BoundVar, ClosureKind, ConstVid, FloatTy, FloatVarValue, FloatVid, GenericArgKind, InferConst, InferTy, IntTy, IntVarValue, IntVid, OutlivesPredicate, RegionVid, TyVid, UniverseIndex};
use traits::{ObligationCause, ObligationInspector, PredicateObligations};
use unify_key::{ConstVariableOrigin, ConstVariableValue, ConstVidKey};
pub use BoundRegionConversionTime::*;
pub use RegionVariableOrigin::*;
pub use SubregionOrigin::*;
pub use at::DefineOpaqueTypes;
pub use freshen::TypeFreshener;
use opaque_types::{OpaqueHiddenType, OpaqueTypeStorage};
use region_constraints::{
    GenericKind, RegionConstraintCollector, RegionConstraintStorage, UndoLog, VarInfos, VerifyBound
};
pub use relate::StructurallyRelateAliases;
pub use relate::combine::PredicateEmittingRelation;
use ena::unify as ut;
use rustc_type_ir::solve::Reveal;
use snapshot::undo_log::InferCtxtUndoLogs;
use tracing::{debug, instrument};
use type_variable::TypeVariableOrigin;

use crate::next_solver::fold::BoundVarReplacerDelegate;
use crate::next_solver::{BoundRegion, BoundTy, BoundVarKind};

use super::generics::{GenericParamDef, GenericParamDefKind};
use super::{AliasTerm, Binder, BoundRegionKind, CanonicalQueryInput, CanonicalVarValues, Const, ConstKind, DbInterner, DbIr, ErrorGuaranteed, FxIndexMap, GenericArg, GenericArgs, OpaqueTypeKey, ParamEnv, PlaceholderRegion, PolyCoercePredicate, PolyExistentialProjection, PolyExistentialTraitRef, PolyFnSig, PolyRegionOutlivesPredicate, PolySubtypePredicate, Predicate, Region, Span, SubtypePredicate, Term, TraitPredicate, TraitRef, Ty, TyKind, TypingMode};


pub mod at;
pub mod canonical;
mod context;
mod data_structures;
mod freshen;
mod opaque_types;
mod project;
pub mod region_constraints;
pub mod relate;
pub mod resolve;
pub(crate) mod select;
pub(crate) mod snapshot;
mod traits;
mod type_variable;
mod unify_key;

/// `InferOk<'tcx, ()>` is used a lot. It may seem like a useless wrapper
/// around `PredicateObligations`, but it has one important property:
/// because `InferOk` is marked with `#[must_use]`, if you have a method
/// `InferCtxt::f` that returns `InferResult<()>` and you call it with
/// `infcx.f()?;` you'll get a warning about the obligations being discarded
/// without use, which is probably unintentional and has been a source of bugs
/// in the past.
#[must_use]
#[derive(Debug)]
pub struct InferOk<T> {
    pub value: T,
    pub obligations: PredicateObligations,
}
pub type InferResult<T> = Result<InferOk<T>, TypeError<DbInterner>>;

pub(crate) type FixupResult<T> = Result<T, FixupError>; // "fixup result"

pub(crate) type UnificationTable<'a, T> = ut::UnificationTable<
    ut::InPlace<T, &'a mut ut::UnificationStorage<T>, &'a mut InferCtxtUndoLogs>,
>;

/// This type contains all the things within `InferCtxt` that sit within a
/// `RefCell` and are involved with taking/rolling back snapshots. Snapshot
/// operations are hot enough that we want only one call to `borrow_mut` per
/// call to `start_snapshot` and `rollback_to`.
#[derive(Clone)]
pub struct InferCtxtInner {
    pub(crate) undo_log: InferCtxtUndoLogs,

    /// Cache for projections.
    ///
    /// This cache is snapshotted along with the infcx.
    pub(crate) projection_cache: ProjectionCacheStorage,

    /// We instantiate `UnificationTable` with `bounds<Ty>` because the types
    /// that might instantiate a general type variable have an order,
    /// represented by its upper and lower bounds.
    pub(crate) type_variable_storage: type_variable::TypeVariableStorage,

    /// Map from const parameter variable to the kind of const it represents.
    pub(crate) const_unification_storage: ut::UnificationTableStorage<ConstVidKey>,

    /// Map from integral variable to the kind of integer it represents.
    pub(crate) int_unification_storage: ut::UnificationTableStorage<IntVid>,

    /// Map from floating variable to the kind of float it represents.
    pub(crate) float_unification_storage: ut::UnificationTableStorage<FloatVid>,

    /// Tracks the set of region variables and the constraints between them.
    ///
    /// This is initially `Some(_)` but when
    /// `resolve_regions_and_report_errors` is invoked, this gets set to `None`
    /// -- further attempts to perform unification, etc., may fail if new
    /// region constraints would've been added.
    pub(crate) region_constraint_storage: Option<RegionConstraintStorage>,

    /// A set of constraints that regionck must validate.
    ///
    /// Each constraint has the form `T:'a`, meaning "some type `T` must
    /// outlive the lifetime 'a". These constraints derive from
    /// instantiated type parameters. So if you had a struct defined
    /// like the following:
    /// ```ignore (illustrative)
    /// struct Foo<T: 'static> { ... }
    /// ```
    /// In some expression `let x = Foo { ... }`, it will
    /// instantiate the type parameter `T` with a fresh type `$0`. At
    /// the same time, it will record a region obligation of
    /// `$0: 'static`. This will get checked later by regionck. (We
    /// can't generally check these things right away because we have
    /// to wait until types are resolved.)
    ///
    /// These are stored in a map keyed to the id of the innermost
    /// enclosing fn body / static initializer expression. This is
    /// because the location where the obligation was incurred can be
    /// relevant with respect to which sublifetime assumptions are in
    /// place. The reason that we store under the fn-id, and not
    /// something more fine-grained, is so that it is easier for
    /// regionck to be sure that it has found *all* the region
    /// obligations (otherwise, it's easy to fail to walk to a
    /// particular node-id).
    ///
    /// Before running `resolve_regions_and_report_errors`, the creator
    /// of the inference context is expected to invoke
    /// [`InferCtxt::process_registered_region_obligations`]
    /// for each body-id in this map, which will process the
    /// obligations within. This is expected to be done 'late enough'
    /// that all type inference variables have been bound and so forth.
    pub(crate) region_obligations: Vec<RegionObligation>,

    /// Caches for opaque type inference.
    pub(crate) opaque_type_storage: OpaqueTypeStorage,
}

impl InferCtxtInner {
    fn new() -> InferCtxtInner {
        InferCtxtInner {
            undo_log: InferCtxtUndoLogs::default(),

            projection_cache: Default::default(),
            type_variable_storage: Default::default(),
            const_unification_storage: Default::default(),
            int_unification_storage: Default::default(),
            float_unification_storage: Default::default(),
            region_constraint_storage: Some(Default::default()),
            region_obligations: vec![],
            opaque_type_storage: Default::default(),
        }
    }

    #[inline]
    pub fn region_obligations(&self) -> &[RegionObligation] {
        &self.region_obligations
    }

    #[inline]
    fn try_type_variables_probe_ref(
        &self,
        vid: TyVid,
    ) -> Option<&type_variable::TypeVariableValue> {
        // Uses a read-only view of the unification table, this way we don't
        // need an undo log.
        self.type_variable_storage.eq_relations_ref().try_probe_value(vid)
    }

    #[inline]
    fn type_variables(&mut self) -> type_variable::TypeVariableTable<'_> {
        self.type_variable_storage.with_log(&mut self.undo_log)
    }

    #[inline]
    fn opaque_types(&mut self) -> opaque_types::OpaqueTypeTable<'_> {
        self.opaque_type_storage.with_log(&mut self.undo_log)
    }

    #[inline]
    fn int_unification_table(&mut self) -> UnificationTable<'_, IntVid> {
        self.int_unification_storage.with_log(&mut self.undo_log)
    }

    #[inline]
    fn float_unification_table(&mut self) -> UnificationTable<'_, FloatVid> {
        self.float_unification_storage.with_log(&mut self.undo_log)
    }

    #[inline]
    fn const_unification_table(&mut self) -> UnificationTable<'_, ConstVidKey> {
        self.const_unification_storage.with_log(&mut self.undo_log)
    }

    #[inline]
    pub fn unwrap_region_constraints(&mut self) -> RegionConstraintCollector<'_> {
        self.region_constraint_storage
            .as_mut()
            .expect("region constraints already solved")
            .with_log(&mut self.undo_log)
    }

    // Iterates through the opaque type definitions without taking them; this holds the
    // `InferCtxtInner` lock, so make sure to not do anything with `InferCtxt` side-effects
    // while looping through this.
    pub fn iter_opaque_types(
        &self,
    ) -> impl Iterator<Item = (OpaqueTypeKey, OpaqueHiddenType)> + '_ {
        self.opaque_type_storage.opaque_types.iter().map(|(k, v)| (k.clone(), v.hidden_type.clone()))
    }
}

pub struct InferCtxt<'db> {
    pub ir: DbIr<'db>,

    /// The mode of this inference context, see the struct documentation
    /// for more details.
    typing_mode: TypingMode,

    /// Whether this inference context should care about region obligations in
    /// the root universe. Most notably, this is used during hir typeck as region
    /// solving is left to borrowck instead.
    pub considering_regions: bool,

    /// If set, this flag causes us to skip the 'leak check' during
    /// higher-ranked subtyping operations. This flag is a temporary one used
    /// to manage the removal of the leak-check: for the time being, we still run the
    /// leak-check, but we issue warnings.
    skip_leak_check: bool,

    pub inner: RefCell<InferCtxtInner>,

    /// The set of predicates on which errors have been reported, to
    /// avoid reporting the same error twice.
    pub reported_trait_errors:
        RefCell<FxIndexMap<Span, (Vec<Predicate>, ErrorGuaranteed)>>,

    pub reported_signature_mismatch: RefCell<FxHashSet<(Span, Option<Span>)>>,

    /// When an error occurs, we want to avoid reporting "derived"
    /// errors that are due to this original failure. We have this
    /// flag that one can set whenever one creates a type-error that
    /// is due to an error in a prior pass.
    ///
    /// Don't read this flag directly, call `is_tainted_by_errors()`
    /// and `set_tainted_by_errors()`.
    tainted_by_errors: Cell<Option<ErrorGuaranteed>>,

    /// What is the innermost universe we have created? Starts out as
    /// `UniverseIndex::root()` but grows from there as we enter
    /// universal quantifiers.
    ///
    /// N.B., at present, we exclude the universal quantifiers on the
    /// item we are type-checking, and just consider those names as
    /// part of the root universe. So this would only get incremented
    /// when we enter into a higher-ranked (`for<..>`) type or trait
    /// bound.
    universe: Cell<UniverseIndex>,

    pub obligation_inspector: Cell<Option<ObligationInspector<'db>>>,
}

/// See the `error_reporting` module for more details.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValuePairs {
    Regions(ExpectedFound<Region>),
    Terms(ExpectedFound<Term>),
    Aliases(ExpectedFound<AliasTerm>),
    TraitRefs(ExpectedFound<TraitRef>),
    PolySigs(ExpectedFound<PolyFnSig>),
    ExistentialTraitRef(ExpectedFound<PolyExistentialTraitRef>),
    ExistentialProjection(ExpectedFound<PolyExistentialProjection>),
}

impl ValuePairs {
    pub fn ty(&self) -> Option<(Ty, Ty)> {
        if let ValuePairs::Terms(ExpectedFound { expected, found }) = self {
            if let Some(expected) = expected.as_type() {
                if let Some(found) = found.as_type() {
                    return Some((expected, found));
                }
            }
        }
        None
    }
}

/// The trace designates the path through inference that we took to
/// encounter an error or subtyping constraint.
///
/// See the `error_reporting` module for more details.
#[derive(Clone, Debug)]
pub struct TypeTrace {
    pub cause: ObligationCause,
    pub values: ValuePairs,
}

/// The origin of a `r1 <= r2` constraint.
///
/// See `error_reporting` module for more details
#[derive(Clone, Debug)]
pub enum SubregionOrigin {
    /// Arose from a subtyping relation
    Subtype(Box<TypeTrace>),

    /// When casting `&'a T` to an `&'b Trait` object,
    /// relating `'a` to `'b`.
    RelateObjectBound(Span),

    /// Some type parameter was instantiated with the given type,
    /// and that type must outlive some region.
    RelateParamBound(Span, Ty, Option<Span>),

    /// The given region parameter was instantiated with a region
    /// that must outlive some other region.
    RelateRegionParamBound(Span, Option<Ty>),

    /// Creating a pointer `b` to contents of another reference.
    Reborrow(Span),

    /// (&'a &'b T) where a >= b
    ReferenceOutlivesReferent(Ty, Span),

    /// Comparing the signature and requirements of an impl method against
    /// the containing trait.
    CompareImplItemObligation {
        span: Span,
        impl_item_def_id: GenericDefId,
        trait_item_def_id: GenericDefId,
    },

    /// Checking that the bounds of a trait's associated type hold for a given impl.
    CheckAssociatedTypeBounds {
        parent: Box<SubregionOrigin>,
        impl_item_def_id: GenericDefId,
        trait_item_def_id: GenericDefId,
    },

    AscribeUserTypeProvePredicate(Span),
}

/// Outlives-constraints can be categorized to determine whether and why they
/// are interesting (for error reporting). Order of variants indicates sort
/// order of the category, thereby influencing diagnostic output.
///
/// See also `rustc_const_eval::borrow_check::constraints`.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ConstraintCategory {
    Return,
    Yield,
    UseAsConst,
    UseAsStatic,
    TypeAnnotation,
    Cast {
        /// Whether this cast is a coercion that was automatically inserted by the compiler.
        is_implicit_coercion: bool,
        /// Whether this is an unsizing coercion and if yes, this contains the target type.
        /// Region variables are erased to ReErased.
        unsize_to: Option<Ty>,
    },

    /// A constraint that came from checking the body of a closure.
    ///
    /// We try to get the category that the closure used when reporting this.
    ClosureBounds,

    /// Contains the function type if available.
    CallArgument(Option<Ty>),
    CopyBound,
    SizedBound,
    Assignment,
    /// A constraint that came from a usage of a variable (e.g. in an ADT expression
    /// like `Foo { field: my_val }`)
    Usage,
    OpaqueType,
    ClosureUpvar,

    /// A constraint from a user-written predicate
    /// with the provided span, written on the item
    /// with the given `DefId`
    Predicate(Span),

    /// A "boring" constraint (caused by the given location) is one that
    /// the user probably doesn't want to see described in diagnostics,
    /// because it is kind of an artifact of the type system setup.
    Boring,
    // Boring and applicable everywhere.
    BoringNoLocation,

    /// A constraint that doesn't correspond to anything the user sees.
    Internal,

    /// An internal constraint derived from an illegal universe relation.
    IllegalUniverse,
}

/// Times when we replace bound regions with existentials:
#[derive(Clone, Copy, Debug)]
pub enum BoundRegionConversionTime {
    /// when a fn is called
    FnCall,

    /// when two higher-ranked types are compared
    HigherRankedType,

    /// when projecting an associated type
    AssocTypeProjection(GenericDefId),
}

/// Reasons to create a region inference variable.
///
/// See `error_reporting` module for more details.
#[derive(Clone, Debug)]
pub enum RegionVariableOrigin {
    /// Region variables created for ill-categorized reasons.
    ///
    /// They mostly indicate places in need of refactoring.
    MiscVariable(Span),

    /// Regions created by a `&P` or `[...]` pattern.
    PatternRegion(Span),

    /// Regions created by `&` operator.
    BorrowRegion(Span),

    /// Regions created as part of an autoref of a method receiver.
    Autoref(Span),

    /// Regions created as part of an automatic coercion.
    Coercion(Span),

    /// Region variables created as the values for early-bound regions.
    ///
    /// FIXME(@lcnr): This should also store a `DefId`, similar to
    /// `TypeVariableOrigin`.
    RegionParameterDefinition(Span, Symbol),

    /// Region variables created when instantiating a binder with
    /// existential variables, e.g. when calling a function or method.
    BoundRegion(Span, BoundRegionKind, BoundRegionConversionTime),

    UpvarRegion(Span),

    /// This origin is used for the inference variables that we create
    /// during NLL region processing.
    Nll(NllRegionVariableOrigin),
}

#[derive(Clone, Debug)]
pub enum NllRegionVariableOrigin {
    /// During NLL region processing, we create variables for free
    /// regions that we encounter in the function signature and
    /// elsewhere. This origin indices we've got one of those.
    FreeRegion,

    /// "Universal" instantiation of a higher-ranked region (e.g.,
    /// from a `for<'a> T` binder). Meant to represent "any region".
    Placeholder(PlaceholderRegion),

    Existential {
        /// If this is true, then this variable was created to represent a lifetime
        /// bound in a `for` binder. For example, it might have been created to
        /// represent the lifetime `'a` in a type like `for<'a> fn(&'a u32)`.
        /// Such variables are created when we are trying to figure out if there
        /// is any valid instantiation of `'a` that could fit into some scenario.
        ///
        /// This is used to inform error reporting: in the case that we are trying to
        /// determine whether there is any valid instantiation of a `'a` variable that meets
        /// some constraint C, we want to blame the "source" of that `for` type,
        /// rather than blaming the source of the constraint C.
        from_forall: bool,
    },
}

#[derive(Copy, Clone, Debug)]
pub struct FixupError {
    unresolved: TyOrConstInferVar,
}

impl fmt::Display for FixupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TyOrConstInferVar::*;

        match self.unresolved {
            TyInt(_) => write!(
                f,
                "cannot determine the type of this integer; \
                 add a suffix to specify the type explicitly"
            ),
            TyFloat(_) => write!(
                f,
                "cannot determine the type of this number; \
                 add a suffix to specify the type explicitly"
            ),
            Ty(_) => write!(f, "unconstrained type"),
            Const(_) => write!(f, "unconstrained const value"),
        }
    }
}

/// See the `region_obligations` field for more information.
#[derive(Clone, Debug)]
pub struct RegionObligation {
    pub sub_region: Region,
    pub sup_type: Ty,
    pub origin: SubregionOrigin,
}

/// Used to configure inference contexts before their creation.
pub struct InferCtxtBuilder<'db> {
    ir: DbIr<'db>,
    considering_regions: bool,
    skip_leak_check: bool,
}

#[extension(pub trait DbInternerInferExt)]
impl<'db> DbIr<'db> {
    fn infer_ctxt(self) -> InferCtxtBuilder<'db> {
        InferCtxtBuilder {
            ir: self,
            considering_regions: true,
            skip_leak_check: false,
        }
    }
}

impl<'db> InferCtxtBuilder<'db> {
    pub fn ignoring_regions(mut self) -> Self {
        self.considering_regions = false;
        self
    }

    pub fn skip_leak_check(mut self, skip_leak_check: bool) -> Self {
        self.skip_leak_check = skip_leak_check;
        self
    }

    /// Given a canonical value `C` as a starting point, create an
    /// inference context that contains each of the bound values
    /// within instantiated as a fresh variable. The `f` closure is
    /// invoked with the new infcx, along with the instantiated value
    /// `V` and a instantiation `S`. This instantiation `S` maps from
    /// the bound values in `C` to their instantiated values in `V`
    /// (in other words, `S(C) = V`).
    pub fn build_with_canonical<T>(
        mut self,
        span: Span,
        input: &CanonicalQueryInput<T>,
    ) -> (InferCtxt<'db>, T, CanonicalVarValues)
    where
        T: TypeFoldable<DbInterner>,
    {
        let infcx = self.build(input.typing_mode.clone());
        let (value, args) = infcx.instantiate_canonical(span, &input.canonical);
        (infcx, value, args)
    }

    pub fn build(&mut self, typing_mode: TypingMode) -> InferCtxt<'db> {
        let InferCtxtBuilder { ir, considering_regions, skip_leak_check } =
            *self;
        InferCtxt {
            ir,
            typing_mode,
            considering_regions,
            skip_leak_check,
            inner: RefCell::new(InferCtxtInner::new()),
            reported_trait_errors: Default::default(),
            reported_signature_mismatch: Default::default(),
            tainted_by_errors: Cell::new(None),
            universe: Cell::new(UniverseIndex::ROOT),
            obligation_inspector: Cell::new(None),
        }
    }
}

impl InferOk<()> {
    pub fn into_obligations(self) -> PredicateObligations {
        self.obligations
    }
}

impl<'db> InferCtxt<'db> {
    #[inline(always)]
    pub fn typing_mode(
        &self,
        param_env_for_debug_assertion: &ParamEnv,
    ) -> TypingMode {
        if cfg!(debug_assertions) {
            match (param_env_for_debug_assertion.reveal(), self.typing_mode.clone()) {
                (Reveal::All, TypingMode::PostAnalysis)
                | (Reveal::UserFacing, TypingMode::Coherence | TypingMode::Analysis { .. }) => {}
                (r, t) => unreachable!("TypingMode x Reveal mismatch: {r:?} {t:?}"),
            }
        }
        self.typing_mode.clone()
    }

    #[inline(always)]
    pub fn typing_mode_unchecked(&self) -> TypingMode {
        self.typing_mode.clone()
    }

    pub fn freshen<T: TypeFoldable<DbInterner>>(&self, t: T) -> T {
        t.fold_with(&mut self.freshener())
    }

    /// Returns the origin of the type variable identified by `vid`.
    ///
    /// No attempt is made to resolve `vid` to its root variable.
    pub fn type_var_origin(&self, vid: TyVid) -> TypeVariableOrigin {
        self.inner.borrow_mut().type_variables().var_origin(vid)
    }

    /// Returns the origin of the const variable identified by `vid`
    // FIXME: We should store origins separately from the unification table
    // so this doesn't need to be optional.
    pub fn const_var_origin(&self, vid: ConstVid) -> Option<ConstVariableOrigin> {
        match self.inner.borrow_mut().const_unification_table().probe_value(vid) {
            ConstVariableValue::Known { .. } => None,
            ConstVariableValue::Unknown { origin, .. } => Some(origin),
        }
    }

    pub fn freshener<'b>(&'b self) -> TypeFreshener<'b, 'db> {
        freshen::TypeFreshener::new(self)
    }

    pub fn unresolved_variables(&self) -> Vec<Ty> {
        let mut inner = self.inner.borrow_mut();
        let mut vars: Vec<Ty> = inner
            .type_variables()
            .unresolved_variables()
            .into_iter()
            .map(|t| Ty::new_var(DbInterner, t))
            .collect();
        vars.extend(
            (0..inner.int_unification_table().len())
                .map(|i| IntVid::from_usize(i))
                .filter(|&vid| inner.int_unification_table().probe_value(vid).is_unknown())
                .map(|v| Ty::new_int_var(v)),
        );
        vars.extend(
            (0..inner.float_unification_table().len())
                .map(|i| FloatVid::from_usize(i))
                .filter(|&vid| inner.float_unification_table().probe_value(vid).is_unknown())
                .map(|v| Ty::new_float_var(v)),
        );
        vars
    }

    #[instrument(skip(self), level = "debug")]
    pub fn sub_regions(
        &self,
        origin: SubregionOrigin,
        a: Region,
        b: Region,
    ) {
        self.inner.borrow_mut().unwrap_region_constraints().make_subregion(origin, a, b);
    }

    /// Require that the region `r` be equal to one of the regions in
    /// the set `regions`.
    #[instrument(skip(self), level = "debug")]
    pub fn member_constraint(
        &self,
        key: OpaqueTypeKey,
        definition_span: Span,
        hidden_ty: Ty,
        region: Region,
        in_regions: Arc<Vec<Region>>,
    ) {
        self.inner.borrow_mut().unwrap_region_constraints().member_constraint(
            key,
            definition_span,
            hidden_ty,
            region,
            in_regions,
        );
    }

    /// Processes a `Coerce` predicate from the fulfillment context.
    /// This is NOT the preferred way to handle coercion, which is to
    /// invoke `FnCtxt::coerce` or a similar method (see `coercion.rs`).
    ///
    /// This method here is actually a fallback that winds up being
    /// invoked when `FnCtxt::coerce` encounters unresolved type variables
    /// and records a coercion predicate. Presently, this method is equivalent
    /// to `subtype_predicate` -- that is, "coercing" `a` to `b` winds up
    /// actually requiring `a <: b`. This is of course a valid coercion,
    /// but it's not as flexible as `FnCtxt::coerce` would be.
    ///
    /// (We may refactor this in the future, but there are a number of
    /// practical obstacles. Among other things, `FnCtxt::coerce` presently
    /// records adjustments that are required on the HIR in order to perform
    /// the coercion, and we don't currently have a way to manage that.)
    pub fn coerce_predicate(
        &self,
        cause: &ObligationCause,
        param_env: ParamEnv,
        predicate: PolyCoercePredicate,
    ) -> Result<InferResult<()>, (TyVid, TyVid)> {
        let subtype_predicate = predicate.map_bound(|p| SubtypePredicate {
            a_is_expected: false, // when coercing from `a` to `b`, `b` is expected
            a: p.a,
            b: p.b,
        });
        self.subtype_predicate(cause, param_env, subtype_predicate)
    }

    pub fn subtype_predicate(
        &self,
        cause: &ObligationCause,
        param_env: ParamEnv,
        predicate: PolySubtypePredicate,
    ) -> Result<InferResult<()>, (TyVid, TyVid)> {
        // Check for two unresolved inference variables, in which case we can
        // make no progress. This is partly a micro-optimization, but it's
        // also an opportunity to "sub-unify" the variables. This isn't
        // *necessary* to prevent cycles, because they would eventually be sub-unified
        // anyhow during generalization, but it helps with diagnostics (we can detect
        // earlier that they are sub-unified).
        //
        // Note that we can just skip the binders here because
        // type variables can't (at present, at
        // least) capture any of the things bound by this binder.
        //
        // Note that this sub here is not just for diagnostics - it has semantic
        // effects as well.
        let r_a = self.shallow_resolve(predicate.clone().skip_binder().a);
        let r_b = self.shallow_resolve(predicate.clone().skip_binder().b);
        match (r_a.kind(), r_b.kind()) {
            (TyKind::Infer(InferTy::TyVar(a_vid)), TyKind::Infer(InferTy::TyVar(b_vid))) => {
                return Err((a_vid, b_vid));
            }
            _ => {}
        }

        self.enter_forall(predicate, |SubtypePredicate { a_is_expected, a, b }| {
            if a_is_expected {
                Ok(self.at(cause, param_env).sub(DefineOpaqueTypes::Yes, a, b))
            } else {
                Ok(self.at(cause, param_env).sup(DefineOpaqueTypes::Yes, b, a))
            }
        })
    }

    pub fn region_outlives_predicate(
        &self,
        cause: &traits::ObligationCause,
        predicate: PolyRegionOutlivesPredicate,
    ) {
        self.enter_forall(predicate, |OutlivesPredicate(r_a, r_b)| {
            let origin = SubregionOrigin::from_obligation_cause(cause, || {
                RelateRegionParamBound(cause.span, None)
            });
            self.sub_regions(origin, r_b, r_a); // `b : a` ==> `a <= b`
        })
    }

    /// Number of type variables created so far.
    pub fn num_ty_vars(&self) -> usize {
        self.inner.borrow_mut().type_variables().num_vars()
    }

    pub fn next_ty_var(&self, span: Span) -> Ty {
        self.next_ty_var_with_origin(TypeVariableOrigin { span, param_def_id: None })
    }

    pub fn next_ty_var_with_origin(&self, origin: TypeVariableOrigin) -> Ty {
        let vid = self.inner.borrow_mut().type_variables().new_var(self.universe(), origin);
        Ty::new_var(DbInterner, vid)
    }

    pub fn next_ty_var_id_in_universe(&self, span: Span, universe: UniverseIndex) -> TyVid {
        let origin = TypeVariableOrigin { span, param_def_id: None };
        self.inner.borrow_mut().type_variables().new_var(universe, origin)
    }

    pub fn next_ty_var_in_universe(&self, span: Span, universe: UniverseIndex) -> Ty {
        let vid = self.next_ty_var_id_in_universe(span, universe);
        Ty::new_var(DbInterner, vid)
    }

    pub fn next_const_var(&self, span: Span) -> Const {
        self.next_const_var_with_origin(ConstVariableOrigin { span, param_def_id: None })
    }

    pub fn next_const_var_with_origin(&self, origin: ConstVariableOrigin) -> Const {
        let vid = self
            .inner
            .borrow_mut()
            .const_unification_table()
            .new_key(ConstVariableValue::Unknown { origin, universe: self.universe() })
            .vid;
        Const::new_var(DbInterner, vid)
    }

    pub fn next_const_var_in_universe(
        &self,
        span: Span,
        universe: UniverseIndex,
    ) -> Const {
        let origin = ConstVariableOrigin { span, param_def_id: None };
        let vid = self
            .inner
            .borrow_mut()
            .const_unification_table()
            .new_key(ConstVariableValue::Unknown { origin, universe })
            .vid;
        Const::new_var(DbInterner, vid)
    }

    pub fn next_int_var(&self) -> Ty {
        let next_int_var_id =
            self.inner.borrow_mut().int_unification_table().new_key(IntVarValue::Unknown);
        Ty::new_int_var(next_int_var_id)
    }

    pub fn next_float_var(&self) -> Ty {
        let next_float_var_id =
            self.inner.borrow_mut().float_unification_table().new_key(FloatVarValue::Unknown);
        Ty::new_float_var(next_float_var_id)
    }

    /// Creates a fresh region variable with the next available index.
    /// The variable will be created in the maximum universe created
    /// thus far, allowing it to name any region created thus far.
    pub fn next_region_var(&self, origin: RegionVariableOrigin) -> Region {
        self.next_region_var_in_universe(origin, self.universe())
    }

    /// Creates a fresh region variable with the next available index
    /// in the given universe; typically, you can use
    /// `next_region_var` and just use the maximal universe.
    pub fn next_region_var_in_universe(
        &self,
        origin: RegionVariableOrigin,
        universe: UniverseIndex,
    ) -> Region {
        let region_var =
            self.inner.borrow_mut().unwrap_region_constraints().new_region_var(universe, origin);
        Region::new_var(region_var)
    }

    /// Return the universe that the region `r` was created in. For
    /// most regions (e.g., `'static`, named regions from the user,
    /// etc) this is the root universe U0. For inference variables or
    /// placeholders, however, it will return the universe which they
    /// are associated.
    pub fn universe_of_region(&self, r: Region) -> UniverseIndex {
        self.inner.borrow_mut().unwrap_region_constraints().universe(r)
    }

    /// Number of region variables created so far.
    pub fn num_region_vars(&self) -> usize {
        self.inner.borrow_mut().unwrap_region_constraints().num_region_vars()
    }

    /// Just a convenient wrapper of `next_region_var` for using during NLL.
    #[instrument(skip(self), level = "debug")]
    pub fn next_nll_region_var(&self, origin: NllRegionVariableOrigin) -> Region {
        self.next_region_var(RegionVariableOrigin::Nll(origin))
    }

    /// Just a convenient wrapper of `next_region_var` for using during NLL.
    #[instrument(skip(self), level = "debug")]
    pub fn next_nll_region_var_in_universe(
        &self,
        origin: NllRegionVariableOrigin,
        universe: UniverseIndex,
    ) -> Region {
        self.next_region_var_in_universe(RegionVariableOrigin::Nll(origin), universe)
    }

    pub fn var_for_def(&self, span: Span, param: &GenericParamDef) -> GenericArg {
        match param.kind {
            GenericParamDefKind::Lifetime => {
                // Create a region inference variable for the given
                // region parameter definition.
                self.next_region_var(RegionParameterDefinition(span, param.name.clone())).into()
            }
            GenericParamDefKind::Type { .. } => {
                // Create a type inference variable for the given
                // type parameter definition. The generic parameters are
                // for actual parameters that may be referred to by
                // the default of this type parameter, if it exists.
                // e.g., `struct Foo<A, B, C = (A, B)>(...);` when
                // used in a path such as `Foo::<T, U>::new()` will
                // use an inference variable for `C` with `[T, U]`
                // as the generic parameters for the default, `(T, U)`.
                let ty_var_id = self.inner.borrow_mut().type_variables().new_var(
                    self.universe(),
                    //TypeVariableOrigin { param_def_id: Some(param.def_id), span },
                    TypeVariableOrigin { param_def_id: None, span },
                );

                Ty::new_var(DbInterner, ty_var_id).into()
            }
            GenericParamDefKind::Const { .. } => {
                //let origin = ConstVariableOrigin { param_def_id: Some(param.def_id), span };
                let origin = ConstVariableOrigin { param_def_id: None, span };
                let const_var_id = self
                    .inner
                    .borrow_mut()
                    .const_unification_table()
                    .new_key(ConstVariableValue::Unknown { origin, universe: self.universe() })
                    .vid;
                Const::new_var(DbInterner, const_var_id).into()
            }
        }
    }

    /// Given a set of generics defined on a type or impl, returns the generic parameters mapping
    /// each type/region parameter to a fresh inference variable.
    pub fn fresh_args_for_item(&self, span: Span, def_id: GenericDefId) -> GenericArgs {
        GenericArgs::for_item(self.ir, def_id, |param, _| self.var_for_def(span, param))
    }

    /// Returns `true` if errors have been reported since this infcx was
    /// created. This is sometimes used as a heuristic to skip
    /// reporting errors that often occur as a result of earlier
    /// errors, but where it's hard to be 100% sure (e.g., unresolved
    /// inference variables, regionck errors).
    #[must_use = "this method does not have any side effects"]
    pub fn tainted_by_errors(&self) -> Option<ErrorGuaranteed> {
        self.tainted_by_errors.get()
    }

    /// Set the "tainted by errors" flag to true. We call this when we
    /// observe an error from a prior pass.
    pub fn set_tainted_by_errors(&self, e: ErrorGuaranteed) {
        debug!("set_tainted_by_errors(ErrorGuaranteed)");
        self.tainted_by_errors.set(Some(e));
    }

    pub fn region_var_origin(&self, vid: RegionVid) -> RegionVariableOrigin {
        let mut inner = self.inner.borrow_mut();
        let inner = &mut *inner;
        inner.unwrap_region_constraints().var_origin(vid)
    }

    /// Clone the list of variable regions. This is used only during NLL processing
    /// to put the set of region variables into the NLL region context.
    pub fn get_region_var_origins(&self) -> VarInfos {
        let inner = self.inner.borrow();
        assert!(!UndoLogs::<UndoLog>::in_snapshot(&inner.undo_log));
        let storage = inner.region_constraint_storage.as_ref().expect("regions already resolved");
        assert!(storage.data.is_empty());
        // We clone instead of taking because borrowck still wants to use the
        // inference context after calling this for diagnostics and the new
        // trait solver.
        storage.var_infos.clone()
    }

    #[instrument(level = "debug", skip(self), ret)]
    pub fn take_opaque_types(&self) -> opaque_types::OpaqueTypeMap {
        std::mem::take(&mut self.inner.borrow_mut().opaque_type_storage.opaque_types)
    }

    #[instrument(level = "debug", skip(self), ret)]
    pub fn clone_opaque_types(&self) -> opaque_types::OpaqueTypeMap {
        self.inner.borrow().opaque_type_storage.opaque_types.clone()
    }

    #[inline(always)]
    pub fn can_define_opaque_ty(&self, id: impl Into<GenericDefId>) -> bool {
        match self.typing_mode_unchecked() {
            TypingMode::Analysis { defining_opaque_types } => {
                defining_opaque_types.contains(&id.into())
            }
            TypingMode::Coherence | TypingMode::PostAnalysis => false,
        }
    }

    /// If `TyVar(vid)` resolves to a type, return that type. Else, return the
    /// universe index of `TyVar(vid)`.
    pub fn probe_ty_var(&self, vid: TyVid) -> Result<Ty, UniverseIndex> {
        use self::type_variable::TypeVariableValue;

        match self.inner.borrow_mut().type_variables().probe(vid) {
            TypeVariableValue::Known { value } => Ok(value),
            TypeVariableValue::Unknown { universe } => Err(universe),
        }
    }

    pub fn shallow_resolve(&self, ty: Ty) -> Ty {
        if let TyKind::Infer(v) = ty.clone().kind() {
            match v {
                InferTy::TyVar(v) => {
                    // Not entirely obvious: if `typ` is a type variable,
                    // it can be resolved to an int/float variable, which
                    // can then be recursively resolved, hence the
                    // recursion. Note though that we prevent type
                    // variables from unifying to other type variables
                    // directly (though they may be embedded
                    // structurally), and we prevent cycles in any case,
                    // so this recursion should always be of very limited
                    // depth.
                    //
                    // Note: if these two lines are combined into one we get
                    // dynamic borrow errors on `self.inner`.
                    let known = self.inner.borrow_mut().type_variables().probe(v).known();
                    known.map_or(ty, |t| self.shallow_resolve(t))
                }

                InferTy::IntVar(v) => {
                    match self.inner.borrow_mut().int_unification_table().probe_value(v) {
                        IntVarValue::IntType(ty) => Ty::new_int(ty),
                        IntVarValue::UintType(ty) => Ty::new_uint(ty),
                        IntVarValue::Unknown => ty,
                    }
                }

                InferTy::FloatVar(v) => {
                    match self.inner.borrow_mut().float_unification_table().probe_value(v) {
                        FloatVarValue::Known(ty) => Ty::new_float(ty),
                        FloatVarValue::Unknown => ty,
                    }
                }

                InferTy::FreshTy(_) | InferTy::FreshIntTy(_) | InferTy::FreshFloatTy(_) => ty,
            }
        } else {
            ty
        }
    }

    pub fn shallow_resolve_const(&self, ct: Const) -> Const {
        match ct.clone().kind() {
            ConstKind::Infer(infer_ct) => match infer_ct {
                InferConst::Var(vid) => self
                    .inner
                    .borrow_mut()
                    .const_unification_table()
                    .probe_value(vid)
                    .known()
                    .unwrap_or(ct),
                InferConst::Fresh(_) => ct,
            },
            ConstKind::Param(_)
            | ConstKind::Bound(_, _)
            | ConstKind::Placeholder(_)
            | ConstKind::Unevaluated(_)
            | ConstKind::Value(_, _)
            | ConstKind::Error(_)
            | ConstKind::Expr(_) => ct,
        }
    }

    pub fn root_var(&self, var: TyVid) -> TyVid {
        self.inner.borrow_mut().type_variables().root_var(var)
    }

    pub fn root_const_var(&self, var: ConstVid) -> ConstVid {
        self.inner.borrow_mut().const_unification_table().find(var).vid
    }

    /// Resolves an int var to a rigid int type, if it was constrained to one,
    /// or else the root int var in the unification table.
    pub fn opportunistic_resolve_int_var(&self, vid: IntVid) -> Ty {
        let mut inner = self.inner.borrow_mut();
        let value = inner.int_unification_table().probe_value(vid);
        match value {
            IntVarValue::IntType(ty) => Ty::new_int(ty),
            IntVarValue::UintType(ty) => Ty::new_uint(ty),
            IntVarValue::Unknown => {
                Ty::new_int_var(inner.int_unification_table().find(vid))
            }
        }
    }

    /// Resolves a float var to a rigid int type, if it was constrained to one,
    /// or else the root float var in the unification table.
    pub fn opportunistic_resolve_float_var(&self, vid: FloatVid) -> Ty {
        let mut inner = self.inner.borrow_mut();
        let value = inner.float_unification_table().probe_value(vid);
        match value {
            FloatVarValue::Known(ty) => Ty::new_float(ty),
            FloatVarValue::Unknown => {
                Ty::new_float_var(inner.float_unification_table().find(vid))
            }
        }
    }

    /// Where possible, replaces type/const variables in
    /// `value` with their final value. Note that region variables
    /// are unaffected. If a type/const variable has not been unified, it
    /// is left as is. This is an idempotent operation that does
    /// not affect inference state in any way and so you can do it
    /// at will.
    pub fn resolve_vars_if_possible<T>(&self, value: T) -> T
    where
        T: TypeFoldable<DbInterner>,
    {
        if let Err(guar) = value.error_reported() {
            self.set_tainted_by_errors(guar);
        }
        if !value.has_non_region_infer() {
            return value;
        }
        let mut r = resolve::OpportunisticVarResolver::new(self);
        value.fold_with(&mut r)
    }

    pub fn resolve_numeric_literals_with_default<T>(&self, value: T) -> T
    where
        T: TypeFoldable<DbInterner>,
    {
        if !value.has_infer() {
            return value; // Avoid duplicated type-folding.
        }
        let mut r = InferenceLiteralEraser { tcx: DbInterner };
        value.fold_with(&mut r)
    }

    pub fn probe_const_var(&self, vid: ConstVid) -> Result<Const, UniverseIndex> {
        match self.inner.borrow_mut().const_unification_table().probe_value(vid) {
            ConstVariableValue::Known { value } => Ok(value),
            ConstVariableValue::Unknown { origin: _, universe } => Err(universe),
        }
    }

    /// Attempts to resolve all type/region/const variables in
    /// `value`. Region inference must have been run already (e.g.,
    /// by calling `resolve_regions_and_report_errors`). If some
    /// variable was never unified, an `Err` results.
    ///
    /// This method is idempotent, but it not typically not invoked
    /// except during the writeback phase.
    pub fn fully_resolve<T: TypeFoldable<DbInterner>>(&self, value: T) -> FixupResult<T> {
        match resolve::fully_resolve(self, value) {
            Ok(value) => {
                if value.has_non_region_infer() || value.has_infer_regions() {
                    panic!("`{value:?}` is not fully resolved");
                }
                Ok(value)
            }
            Err(e) => Err(e),
        }
    }

    // Instantiates the bound variables in a given binder with fresh inference
    // variables in the current universe.
    //
    // Use this method if you'd like to find some generic parameters of the binder's
    // variables (e.g. during a method call). If there isn't a [`BoundRegionConversionTime`]
    // that corresponds to your use case, consider whether or not you should
    // use [`InferCtxt::enter_forall`] instead.
    pub fn instantiate_binder_with_fresh_vars<T>(
        &self,
        span: Span,
        lbrct: BoundRegionConversionTime,
        value: Binder<T>,
    ) -> T
    where
        T: TypeFoldable<DbInterner> + Clone,
    {
        if let Some(inner) = value.clone().no_bound_vars() {
            return inner;
        }

        let bound_vars = value.clone().bound_vars();
        let mut args = Vec::with_capacity(bound_vars.len());

        for bound_var_kind in bound_vars {
            let arg: GenericArg = match bound_var_kind {
                BoundVarKind::Ty(_) => self.next_ty_var(span).into(),
                BoundVarKind::Region(br) => {
                    self.next_region_var(BoundRegion(span, br, lbrct)).into()
                }
                BoundVarKind::Const => self.next_const_var(span).into(),
            };
            args.push(arg);
        }

        struct ToFreshVars {
            args: Vec<GenericArg>,
        }

        impl BoundVarReplacerDelegate for ToFreshVars {
            fn replace_region(&mut self, br: BoundRegion) -> Region {
                self.args[br.var.index()].expect_region()
            }
            fn replace_ty(&mut self, bt: BoundTy) -> Ty {
                self.args[bt.var.index()].expect_ty()
            }
            fn replace_const(&mut self, bv: BoundVar) -> Const {
                self.args[bv.index()].expect_const()
            }
        }
        let delegate = ToFreshVars { args };
        DbInterner.replace_bound_vars_uncached(value, delegate)
    }

    /// See the [`region_constraints::RegionConstraintCollector::verify_generic_bound`] method.
    pub(crate) fn verify_generic_bound(
        &self,
        origin: SubregionOrigin,
        kind: GenericKind,
        a: Region,
        bound: VerifyBound,
    ) {
        debug!("verify_generic_bound({:?}, {:?} <: {:?})", kind, a, bound);

        self.inner
            .borrow_mut()
            .unwrap_region_constraints()
            .verify_generic_bound(origin, kind, a, bound);
    }

    /// Obtains the latest type of the given closure; this may be a
    /// closure in the current function, in which case its
    /// `ClosureKind` may not yet be known.
    pub fn closure_kind(&self, closure_ty: Ty) -> Option<ClosureKind> {
        let unresolved_kind_ty = match closure_ty.clone().kind() {
            TyKind::Closure(_, args) => args.as_closure().kind_ty(),
            TyKind::CoroutineClosure(_, args) => args.as_coroutine_closure().kind_ty(),
            _ => panic!("unexpected type {closure_ty:?}"),
        };
        let closure_kind_ty = self.shallow_resolve(unresolved_kind_ty);
        closure_kind_ty.to_opt_closure_kind()
    }

    pub fn universe(&self) -> UniverseIndex {
        self.universe.get()
    }

    /// Creates and return a fresh universe that extends all previous
    /// universes. Updates `self.universe` to that new universe.
    pub fn create_next_universe(&self) -> UniverseIndex {
        let u = self.universe.get().next_universe();
        debug!("create_next_universe {u:?}");
        self.universe.set(u);
        u
    }

    /// The returned function is used in a fast path. If it returns `true` the variable is
    /// unchanged, `false` indicates that the status is unknown.
    #[inline]
    pub fn is_ty_infer_var_definitely_unchanged<'a>(
        &'a self,
    ) -> (impl Fn(TyOrConstInferVar) -> bool + Captures<'db> + 'a) {
        // This hoists the borrow/release out of the loop body.
        let inner = self.inner.try_borrow();

        move |infer_var: TyOrConstInferVar| match (infer_var, &inner) {
            (TyOrConstInferVar::Ty(ty_var), Ok(inner)) => {
                use self::type_variable::TypeVariableValue;

                matches!(
                    inner.try_type_variables_probe_ref(ty_var),
                    Some(TypeVariableValue::Unknown { .. })
                )
            }
            _ => false,
        }
    }

    /// `ty_or_const_infer_var_changed` is equivalent to one of these two:
    ///   * `shallow_resolve(ty) != ty` (where `ty.kind = Infer(_)`)
    ///   * `shallow_resolve(ct) != ct` (where `ct.kind = ConstKind::Infer(_)`)
    ///
    /// However, `ty_or_const_infer_var_changed` is more efficient. It's always
    /// inlined, despite being large, because it has only two call sites that
    /// are extremely hot (both in `traits::fulfill`'s checking of `stalled_on`
    /// inference variables), and it handles both `Ty` and `Const` without
    /// having to resort to storing full `GenericArg`s in `stalled_on`.
    #[inline(always)]
    pub fn ty_or_const_infer_var_changed(&self, infer_var: TyOrConstInferVar) -> bool {
        match infer_var {
            TyOrConstInferVar::Ty(v) => {
                use self::type_variable::TypeVariableValue;

                // If `inlined_probe` returns a `Known` value, it never equals
                // `Infer(TyVar(v))`.
                match self.inner.borrow_mut().type_variables().inlined_probe(v) {
                    TypeVariableValue::Unknown { .. } => false,
                    TypeVariableValue::Known { .. } => true,
                }
            }

            TyOrConstInferVar::TyInt(v) => {
                // If `inlined_probe_value` returns a value it's always a
                // `Int(_)` or `UInt(_)`, which never matches a
                // `Infer(_)`.
                self.inner.borrow_mut().int_unification_table().inlined_probe_value(v).is_known()
            }

            TyOrConstInferVar::TyFloat(v) => {
                // If `probe_value` returns a value it's always a
                // `Float(_)`, which never matches a `Infer(_)`.
                //
                // Not `inlined_probe_value(v)` because this call site is colder.
                self.inner.borrow_mut().float_unification_table().probe_value(v).is_known()
            }

            TyOrConstInferVar::Const(v) => {
                // If `probe_value` returns a `Known` value, it never equals
                // `ConstKind::Infer(InferConst::Var(v))`.
                //
                // Not `inlined_probe_value(v)` because this call site is colder.
                match self.inner.borrow_mut().const_unification_table().probe_value(v) {
                    ConstVariableValue::Unknown { .. } => false,
                    ConstVariableValue::Known { .. } => true,
                }
            }
        }
    }

    /// Attach a callback to be invoked on each root obligation evaluated in the new trait solver.
    pub fn attach_obligation_inspector(&self, inspector: ObligationInspector<'db>) {
        debug_assert!(
            self.obligation_inspector.get().is_none(),
            "shouldn't override a set obligation inspector"
        );
        self.obligation_inspector.set(Some(inspector));
    }
}

/// Helper for [InferCtxt::ty_or_const_infer_var_changed] (see comment on that), currently
/// used only for `traits::fulfill`'s list of `stalled_on` inference variables.
#[derive(Copy, Clone, Debug)]
pub enum TyOrConstInferVar {
    /// Equivalent to `Infer(TyVar(_))`.
    Ty(TyVid),
    /// Equivalent to `Infer(IntVar(_))`.
    TyInt(IntVid),
    /// Equivalent to `Infer(FloatVar(_))`.
    TyFloat(FloatVid),

    /// Equivalent to `ConstKind::Infer(InferConst::Var(_))`.
    Const(ConstVid),
}

impl TyOrConstInferVar {
    /// Tries to extract an inference variable from a type or a constant, returns `None`
    /// for types other than `Infer(_)` (or `InferTy::Fresh*`) and
    /// for constants other than `ConstKind::Infer(_)` (or `InferConst::Fresh`).
    pub fn maybe_from_generic_arg(arg: GenericArg) -> Option<Self> {
        match arg.kind() {
            GenericArgKind::Type(ty) => Self::maybe_from_ty(ty),
            GenericArgKind::Const(ct) => Self::maybe_from_const(ct),
            GenericArgKind::Lifetime(_) => None,
        }
    }

    /// Tries to extract an inference variable from a type, returns `None`
    /// for types other than `Infer(_)` (or `InferTy::Fresh*`).
    fn maybe_from_ty(ty: Ty) -> Option<Self> {
        match ty.kind() {
            TyKind::Infer(InferTy::TyVar(v)) => Some(TyOrConstInferVar::Ty(v)),
            TyKind::Infer(InferTy::IntVar(v)) => Some(TyOrConstInferVar::TyInt(v)),
            TyKind::Infer(InferTy::FloatVar(v)) => Some(TyOrConstInferVar::TyFloat(v)),
            _ => None,
        }
    }

    /// Tries to extract an inference variable from a constant, returns `None`
    /// for constants other than `ConstKind::Infer(_)` (or `InferConst::Fresh`).
    fn maybe_from_const(ct: Const) -> Option<Self> {
        match ct.kind() {
            ConstKind::Infer(InferConst::Var(v)) => Some(TyOrConstInferVar::Const(v)),
            _ => None,
        }
    }
}

/// Replace `{integer}` with `i32` and `{float}` with `f64`.
/// Used only for diagnostics.
struct InferenceLiteralEraser {
    tcx: DbInterner,
}

impl TypeFolder<DbInterner> for InferenceLiteralEraser {
    fn cx(&self) -> DbInterner {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty) -> Ty {
        match ty.clone().kind() {
            TyKind::Infer(InferTy::IntVar(_) | InferTy::FreshIntTy(_)) => Ty::new_int(IntTy::I32),
            TyKind::Infer(InferTy::FloatVar(_) | InferTy::FreshFloatTy(_)) => Ty::new_float(FloatTy::F64),
            _ => ty.super_fold_with(self),
        }
    }
}

impl TypeTrace {
    pub fn span(&self) -> Span {
        self.cause.span
    }

    pub fn types(
        cause: &ObligationCause,
        a_is_expected: bool,
        a: Ty,
        b: Ty,
    ) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Terms(ExpectedFound::new(a_is_expected, a.into(), b.into())),
        }
    }

    pub fn trait_refs(
        cause: &ObligationCause,
        a_is_expected: bool,
        a: TraitRef,
        b: TraitRef,
    ) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::TraitRefs(ExpectedFound::new(a_is_expected, a, b)),
        }
    }

    pub fn consts(
        cause: &ObligationCause,
        a_is_expected: bool,
        a: Const,
        b: Const,
    ) -> TypeTrace {
        TypeTrace {
            cause: cause.clone(),
            values: ValuePairs::Terms(ExpectedFound::new(a_is_expected, a.into(), b.into())),
        }
    }
}

impl SubregionOrigin {
    pub fn span(&self) -> Span {
        match *self {
            Subtype(ref a) => a.span(),
            RelateObjectBound(a) => a,
            RelateParamBound(a, ..) => a,
            RelateRegionParamBound(a, _) => a,
            Reborrow(a) => a,
            ReferenceOutlivesReferent(_, a) => a,
            CompareImplItemObligation { span, .. } => span,
            AscribeUserTypeProvePredicate(span) => span,
            CheckAssociatedTypeBounds { ref parent, .. } => parent.span(),
        }
    }

    pub fn from_obligation_cause<F>(cause: &traits::ObligationCause, default: F) -> Self
    where
        F: FnOnce() -> Self,
    {
        default()
        /*
        match *cause.code() {
            ObligationCauseCode::ReferenceOutlivesReferent(ref_type) => {
                SubregionOrigin::ReferenceOutlivesReferent(ref_type, cause.span)
            }

            ObligationCauseCode::CompareImplItem {
                impl_item_def_id,
                trait_item_def_id,
                kind: _,
            } => SubregionOrigin::CompareImplItemObligation {
                span: cause.span,
                impl_item_def_id,
                trait_item_def_id,
            },

            ObligationCauseCode::CheckAssociatedTypeBounds {
                impl_item_def_id,
                trait_item_def_id,
            } => SubregionOrigin::CheckAssociatedTypeBounds {
                impl_item_def_id,
                trait_item_def_id,
                parent: Box::new(default()),
            },

            ObligationCauseCode::AscribeUserTypeProvePredicate(span) => {
                SubregionOrigin::AscribeUserTypeProvePredicate(span)
            }

            ObligationCauseCode::ObjectTypeBound(ty, _reg) => {
                SubregionOrigin::RelateRegionParamBound(cause.span, Some(ty))
            }

            _ => default(),
        }
        */
    }
}

impl RegionVariableOrigin {
    pub fn span(&self) -> Span {
        match *self {
            RegionVariableOrigin::MiscVariable(a)
            | RegionVariableOrigin::PatternRegion(a)
            | RegionVariableOrigin::BorrowRegion(a)
            | RegionVariableOrigin::Autoref(a)
            | RegionVariableOrigin::Coercion(a)
            | RegionVariableOrigin::RegionParameterDefinition(a, ..)
            | RegionVariableOrigin::BoundRegion(a, ..)
            | RegionVariableOrigin::UpvarRegion(a) => a,
            RegionVariableOrigin::Nll(..) => panic!("NLL variable used with `span`"),
        }
    }
}

/// Requires that `region` must be equal to one of the regions in `choice_regions`.
/// We often denote this using the syntax:
///
/// ```text
/// R0 member of [O1..On]
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemberConstraint {
    /// The `DefId` and args of the opaque type causing this constraint.
    /// Used for error reporting.
    pub key: OpaqueTypeKey,

    /// The span where the hidden type was instantiated.
    pub definition_span: Span,

    /// The hidden type in which `member_region` appears: used for error reporting.
    pub hidden_ty: Ty,

    /// The region `R0`.
    pub member_region: Region,

    /// The options `O1..On`.
    pub choice_regions: Arc<Vec<Region>>,
}
