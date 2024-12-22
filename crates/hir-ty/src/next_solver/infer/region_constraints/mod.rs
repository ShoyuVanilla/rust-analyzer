//! See `README.md`.

use std::ops::Range;
use std::sync::Arc;
use std::{cmp, fmt, mem};

use ena::undo_log::{Rollback, UndoLogs};
use ena::unify as ut;
use rustc_hash::FxHashMap;
use rustc_index_in_tree::IndexVec;
use rustc_type_ir::inherent::IntoKind;
use rustc_type_ir::{RegionKind, RegionVid, UniverseIndex};
use tracing::{debug, instrument};

use self::CombineMapType::*;
use self::UndoLog::*;
use super::unify_key::RegionVidKey;
use super::{MemberConstraint, MiscVariable, RegionVariableOrigin, SubregionOrigin};
use crate::next_solver::infer::snapshot::undo_log::{InferCtxtUndoLogs, Snapshot};
use crate::next_solver::infer::unify_key::RegionVariableValue;
use crate::next_solver::{AliasTy, Binder, DbInterner, DbIr, OpaqueTypeKey, ParamTy, PlaceholderTy, Region, Span, Ty};

#[derive(Clone, Default)]
pub struct RegionConstraintStorage {
    /// For each `RegionVid`, the corresponding `RegionVariableOrigin`.
    pub(super) var_infos: IndexVec<RegionVid, RegionVariableInfo>,

    pub(super) data: RegionConstraintData,

    /// For a given pair of regions (R1, R2), maps to a region R3 that
    /// is designated as their LUB (edges R1 <= R3 and R2 <= R3
    /// exist). This prevents us from making many such regions.
    lubs: CombineMap,

    /// For a given pair of regions (R1, R2), maps to a region R3 that
    /// is designated as their GLB (edges R3 <= R1 and R3 <= R2
    /// exist). This prevents us from making many such regions.
    glbs: CombineMap,

    /// When we add a R1 == R2 constraint, we currently add (a) edges
    /// R1 <= R2 and R2 <= R1 and (b) we unify the two regions in this
    /// table. You can then call `opportunistic_resolve_var` early
    /// which will map R1 and R2 to some common region (i.e., either
    /// R1 or R2). This is important when fulfillment, dropck and other such
    /// code is iterating to a fixed point, because otherwise we sometimes
    /// would wind up with a fresh stream of region variables that have been
    /// equated but appear distinct.
    pub(super) unification_table: ut::UnificationTableStorage<RegionVidKey>,

    /// a flag set to true when we perform any unifications; this is used
    /// to micro-optimize `take_and_reset_data`
    any_unifications: bool,
}

pub struct RegionConstraintCollector<'a> {
    storage: &'a mut RegionConstraintStorage,
    undo_log: &'a mut InferCtxtUndoLogs,
}

pub type VarInfos = IndexVec<RegionVid, RegionVariableInfo>;

/// The full set of region constraints gathered up by the collector.
/// Describes constraints between the region variables and other
/// regions, as well as other conditions that must be verified, or
/// assumptions that can be made.
#[derive(Debug, Default, Clone)]
pub struct RegionConstraintData {
    /// Constraints of the form `A <= B`, where either `A` or `B` can
    /// be a region variable (or neither, as it happens).
    pub constraints: Vec<(Constraint, SubregionOrigin)>,

    /// Constraints of the form `R0 member of [R1, ..., Rn]`, meaning that
    /// `R0` must be equal to one of the regions `R1..Rn`. These occur
    /// with `impl Trait` quite frequently.
    pub member_constraints: Vec<MemberConstraint>,

    /// A "verify" is something that we need to verify after inference
    /// is done, but which does not directly affect inference in any
    /// way.
    ///
    /// An example is a `A <= B` where neither `A` nor `B` are
    /// inference variables.
    pub verifys: Vec<Verify>,
}

/// Represents a constraint that influences the inference process.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum Constraint {
    /// A region variable is a subregion of another.
    VarSubVar(RegionVid, RegionVid),

    /// A concrete region is a subregion of region variable.
    RegSubVar(Region, RegionVid),

    /// A region variable is a subregion of a concrete region. This does not
    /// directly affect inference, but instead is checked after
    /// inference is complete.
    VarSubReg(RegionVid, Region),

    /// A constraint where neither side is a variable. This does not
    /// directly affect inference, but instead is checked after
    /// inference is complete.
    RegSubReg(Region, Region),
}

impl Constraint {
    pub fn involves_placeholders(&self) -> bool {
        match self {
            Constraint::VarSubVar(_, _) => false,
            Constraint::VarSubReg(_, r) | Constraint::RegSubVar(r, _) => r.is_placeholder(),
            Constraint::RegSubReg(r, s) => r.is_placeholder() || s.is_placeholder(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Verify {
    pub kind: GenericKind,
    pub origin: SubregionOrigin,
    pub region: Region,
    pub bound: VerifyBound,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum GenericKind {
    Param(ParamTy),
    Placeholder(PlaceholderTy),
    Alias(AliasTy),
}

/// Describes the things that some `GenericKind` value `G` is known to
/// outlive. Each variant of `VerifyBound` can be thought of as a
/// function:
/// ```ignore (pseudo-rust)
/// fn(min: Region) -> bool { .. }
/// ```
/// where `true` means that the region `min` meets that `G: min`.
/// (False means nothing.)
///
/// So, for example, if we have the type `T` and we have in scope that
/// `T: 'a` and `T: 'b`, then the verify bound might be:
/// ```ignore (pseudo-rust)
/// fn(min: Region) -> bool {
///    ('a: min) || ('b: min)
/// }
/// ```
/// This is described with an `AnyRegion('a, 'b)` node.
#[derive(Debug, Clone)]
pub enum VerifyBound {
    /// See [`VerifyIfEq`] docs
    IfEq(Binder<VerifyIfEq>),

    /// Given a region `R`, expands to the function:
    ///
    /// ```ignore (pseudo-rust)
    /// fn(min) -> bool {
    ///     R: min
    /// }
    /// ```
    ///
    /// This is used when we can establish that `G: R` -- therefore,
    /// if `R: min`, then by transitivity `G: min`.
    OutlivedBy(Region),

    /// Given a region `R`, true if it is `'empty`.
    IsEmpty,

    /// Given a set of bounds `B`, expands to the function:
    ///
    /// ```ignore (pseudo-rust)
    /// fn(min) -> bool {
    ///     exists (b in B) { b(min) }
    /// }
    /// ```
    ///
    /// In other words, if we meet some bound in `B`, that suffices.
    /// This is used when all the bounds in `B` are known to apply to `G`.
    AnyBound(Vec<VerifyBound>),

    /// Given a set of bounds `B`, expands to the function:
    ///
    /// ```ignore (pseudo-rust)
    /// fn(min) -> bool {
    ///     forall (b in B) { b(min) }
    /// }
    /// ```
    ///
    /// In other words, if we meet *all* bounds in `B`, that suffices.
    /// This is used when *some* bound in `B` is known to suffice, but
    /// we don't know which.
    AllBounds(Vec<VerifyBound>),
}

/// This is a "conditional bound" that checks the result of inference
/// and supplies a bound if it ended up being relevant. It's used in situations
/// like this:
///
/// ```rust,ignore (pseudo-Rust)
/// fn foo<'a, 'b, T: SomeTrait<'a>>
/// where
///    <T as SomeTrait<'a>>::Item: 'b
/// ```
///
/// If we have an obligation like `<T as SomeTrait<'?x>>::Item: 'c`, then
/// we don't know yet whether it suffices to show that `'b: 'c`. If `'?x` winds
/// up being equal to `'a`, then the where-clauses on function applies, and
/// in that case we can show `'b: 'c`. But if `'?x` winds up being something
/// else, the bound isn't relevant.
///
/// In the [`VerifyBound`], this struct is enclosed in `Binder` to account
/// for cases like
///
/// ```rust,ignore (pseudo-Rust)
/// where for<'a> <T as SomeTrait<'a>::Item: 'a
/// ```
///
/// The idea is that we have to find some instantiation of `'a` that can
/// make `<T as SomeTrait<'a>>::Item` equal to the final value of `G`,
/// the generic we are checking.
///
/// ```ignore (pseudo-rust)
/// fn(min) -> bool {
///     exists<'a> {
///         if G == K {
///             B(min)
///         } else {
///             false
///         }
///     }
/// }
/// ```
#[derive(Debug, Clone)]
pub struct VerifyIfEq {
    /// Type which must match the generic `G`
    pub ty: Ty,

    /// Bound that applies if `ty` is equal.
    pub bound: Region,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct TwoRegions {
    a: Region,
    b: Region,
}

#[derive(Clone, PartialEq)]
pub(crate) enum UndoLog {
    /// We added `RegionVid`.
    AddVar(RegionVid),

    /// We added the given `constraint`.
    AddConstraint(usize),

    /// We added the given `verify`.
    AddVerify(usize),

    /// We added a GLB/LUB "combination variable".
    AddCombination(CombineMapType, TwoRegions),
}

#[derive(Clone, PartialEq)]
pub(crate) enum CombineMapType {
    Lub,
    Glb,
}

type CombineMap = FxHashMap<TwoRegions, RegionVid>;

#[derive(Debug, Clone)]
pub struct RegionVariableInfo {
    pub origin: RegionVariableOrigin,
    // FIXME: This is only necessary for `fn take_and_reset_data` and
    // `lexical_region_resolve`. We should rework `lexical_region_resolve`
    // in the near/medium future anyways and could move the unverse info
    // for `fn take_and_reset_data` into a separate table which is
    // only populated when needed.
    //
    // For both of these cases it is fine that this can diverge from the
    // actual universe of the variable, which is directly stored in the
    // unification table for unknown region variables. At some point we could
    // stop emitting bidirectional outlives constraints if equate succeeds.
    // This would be currently unsound as it would cause us to drop the universe
    // changes in `lexical_region_resolve`.
    pub universe: UniverseIndex,
}

pub(crate) struct RegionSnapshot {
    any_unifications: bool,
}

impl RegionConstraintStorage {
    #[inline]
    pub(crate) fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut InferCtxtUndoLogs,
    ) -> RegionConstraintCollector<'a> {
        RegionConstraintCollector { storage: self, undo_log }
    }
}

impl RegionConstraintCollector<'_> {
    pub fn num_region_vars(&self) -> usize {
        self.storage.var_infos.len()
    }

    pub fn region_constraint_data(&self) -> &RegionConstraintData {
        &self.storage.data
    }

    /// Takes (and clears) the current set of constraints. Note that
    /// the set of variables remains intact, but all relationships
    /// between them are reset. This is used during NLL checking to
    /// grab the set of constraints that arose from a particular
    /// operation.
    ///
    /// We don't want to leak relationships between variables between
    /// points because just because (say) `r1 == r2` was true at some
    /// point P in the graph doesn't imply that it will be true at
    /// some other point Q, in NLL.
    ///
    /// Not legal during a snapshot.
    pub fn take_and_reset_data(&mut self) -> RegionConstraintData {
        assert!(!UndoLogs::<UndoLog>::in_snapshot(&self.undo_log));

        // If you add a new field to `RegionConstraintCollector`, you
        // should think carefully about whether it needs to be cleared
        // or updated in some way.
        let RegionConstraintStorage {
            var_infos: _,
            data,
            lubs,
            glbs,
            unification_table: _,
            any_unifications,
        } = self.storage;

        // Clear the tables of (lubs, glbs), so that we will create
        // fresh regions if we do a LUB operation. As it happens,
        // LUB/GLB are not performed by the MIR type-checker, which is
        // the one that uses this method, but it's good to be correct.
        lubs.clear();
        glbs.clear();

        let data = mem::take(data);

        // Clear all unifications and recreate the variables a "now
        // un-unified" state. Note that when we unify `a` and `b`, we
        // also insert `a <= b` and a `b <= a` edges, so the
        // `RegionConstraintData` contains the relationship here.
        if *any_unifications {
            *any_unifications = false;
            // Manually inlined `self.unification_table_mut()` as `self` is used in the closure.
            ut::UnificationTable::with_log(&mut self.storage.unification_table, &mut self.undo_log)
                .reset_unifications(|key| RegionVariableValue::Unknown {
                    universe: self.storage.var_infos[key.vid].universe,
                });
        }

        data
    }

    pub fn data(&self) -> &RegionConstraintData {
        &self.storage.data
    }

    pub(super) fn start_snapshot(&self) -> RegionSnapshot {
        debug!("RegionConstraintCollector: start_snapshot");
        RegionSnapshot { any_unifications: self.storage.any_unifications }
    }

    pub(super) fn rollback_to(&mut self, snapshot: RegionSnapshot) {
        debug!("RegionConstraintCollector: rollback_to({:?})", snapshot);
        self.storage.any_unifications = snapshot.any_unifications;
    }

    pub(super) fn new_region_var(
        &mut self,
        universe: UniverseIndex,
        origin: RegionVariableOrigin,
    ) -> RegionVid {
        let vid = self.storage.var_infos.push(RegionVariableInfo { origin: origin.clone(), universe });

        let u_vid = self.unification_table_mut().new_key(RegionVariableValue::Unknown { universe });
        assert_eq!(vid, u_vid.vid);
        self.undo_log.push(AddVar(vid));
        debug!("created new region variable {:?} in {:?} with origin {:?}", vid, universe, origin);
        vid
    }

    /// Returns the origin for the given variable.
    pub(super) fn var_origin(&self, vid: RegionVid) -> RegionVariableOrigin {
        self.storage.var_infos[vid].origin.clone()
    }

    fn add_constraint(&mut self, constraint: Constraint, origin: SubregionOrigin) {
        // cannot add constraints once regions are resolved
        debug!("RegionConstraintCollector: add_constraint({:?})", constraint);

        let index = self.storage.data.constraints.len();
        self.storage.data.constraints.push((constraint, origin));
        self.undo_log.push(AddConstraint(index));
    }

    fn add_verify(&mut self, verify: Verify) {
        // cannot add verifys once regions are resolved
        debug!("RegionConstraintCollector: add_verify({:?})", verify);

        // skip no-op cases known to be satisfied
        if let VerifyBound::AllBounds(ref bs) = verify.bound {
            if bs.is_empty() {
                return;
            }
        }

        let index = self.storage.data.verifys.len();
        self.storage.data.verifys.push(verify);
        self.undo_log.push(AddVerify(index));
    }

    pub(super) fn make_eqregion(
        &mut self,
        origin: SubregionOrigin,
        a: Region,
        b: Region,
    ) {
        if a != b {
            // Eventually, it would be nice to add direct support for
            // equating regions.
            self.make_subregion(origin.clone(), a.clone(), b.clone());
            self.make_subregion(origin, b.clone(), a.clone());

            match (a.clone().kind(), b.clone().kind()) {
                (RegionKind::ReVar(a), RegionKind::ReVar(b)) => {
                    debug!("make_eqregion: unifying {:?} with {:?}", a, b);
                    if self.unification_table_mut().unify_var_var(a, b).is_ok() {
                        self.storage.any_unifications = true;
                    }
                }
                (RegionKind::ReVar(vid), _) => {
                    debug!("make_eqregion: unifying {:?} with {:?}", vid, b);
                    if self
                        .unification_table_mut()
                        .unify_var_value(vid, RegionVariableValue::Known { value: b })
                        .is_ok()
                    {
                        self.storage.any_unifications = true;
                    };
                }
                (_, RegionKind::ReVar(vid)) => {
                    debug!("make_eqregion: unifying {:?} with {:?}", a, vid);
                    if self
                        .unification_table_mut()
                        .unify_var_value(vid, RegionVariableValue::Known { value: a })
                        .is_ok()
                    {
                        self.storage.any_unifications = true;
                    };
                }
                (_, _) => {}
            }
        }
    }

    pub(super) fn member_constraint(
        &mut self,
        key: OpaqueTypeKey,
        definition_span: Span,
        hidden_ty: Ty,
        member_region: Region,
        choice_regions: Arc<Vec<Region>>,
    ) {
        debug!("member_constraint({:?} in {:#?})", member_region, choice_regions);

        if choice_regions.iter().any(|r| r == &member_region) {
            return;
        }

        self.storage.data.member_constraints.push(MemberConstraint {
            key,
            definition_span,
            hidden_ty,
            member_region,
            choice_regions,
        });
    }

    #[instrument(skip(self, origin), level = "debug")]
    pub(super) fn make_subregion(
        &mut self,
        origin: SubregionOrigin,
        sub: Region,
        sup: Region,
    ) {
        // cannot add constraints once regions are resolved
        debug!("origin = {:#?}", origin);

        match (sub.clone().kind(), sup.clone().kind()) {
            (RegionKind::ReBound(..), _) | (_, RegionKind::ReBound(..)) => {
                panic!("cannot relate bound region: {:?} <= {:?}", sub, sup);
            }
            (_, RegionKind::ReStatic) => {
                // all regions are subregions of static, so we can ignore this
            }
            (RegionKind::ReVar(sub_id), RegionKind::ReVar(sup_id)) => {
                self.add_constraint(Constraint::VarSubVar(sub_id, sup_id), origin);
            }
            (_, RegionKind::ReVar(sup_id)) => {
                self.add_constraint(Constraint::RegSubVar(sub, sup_id), origin);
            }
            (RegionKind::ReVar(sub_id), _) => {
                self.add_constraint(Constraint::VarSubReg(sub_id, sup), origin);
            }
            _ => {
                self.add_constraint(Constraint::RegSubReg(sub, sup), origin);
            }
        }
    }

    pub(super) fn verify_generic_bound(
        &mut self,
        origin: SubregionOrigin,
        kind: GenericKind,
        sub: Region,
        bound: VerifyBound,
    ) {
        self.add_verify(Verify { kind, origin, region: sub, bound });
    }

    pub(super) fn lub_regions(
        &mut self,
        cx: DbIr<'_>,
        origin: SubregionOrigin,
        a: Region,
        b: Region,
    ) -> Region {
        // cannot add constraints once regions are resolved
        debug!("RegionConstraintCollector: lub_regions({:?}, {:?})", a, b);
        if a.is_static() || b.is_static() {
            a // nothing lives longer than static
        } else if a == b {
            a // LUB(a,a) = a
        } else {
            self.combine_vars(cx, Lub, a, b, origin)
        }
    }

    pub(super) fn glb_regions(
        &mut self,
        cx: DbIr<'_>,
        origin: SubregionOrigin,
        a: Region,
        b: Region,
    ) -> Region {
        // cannot add constraints once regions are resolved
        debug!("RegionConstraintCollector: glb_regions({:?}, {:?})", a, b);
        if a.is_static() {
            b // static lives longer than everything else
        } else if b.is_static() {
            a // static lives longer than everything else
        } else if a == b {
            a // GLB(a,a) = a
        } else {
            self.combine_vars(cx, Glb, a, b, origin)
        }
    }

    /// Resolves a region var to its value in the unification table, if it exists.
    /// Otherwise, it is resolved to the root `ReVar` in the table.
    pub fn opportunistic_resolve_var(
        &mut self,
        cx: DbIr<'_>,
        vid: RegionVid,
    ) -> Region {
        let mut ut = self.unification_table_mut();
        let root_vid = ut.find(vid).vid;
        match ut.probe_value(root_vid) {
            RegionVariableValue::Known { value } => value,
            RegionVariableValue::Unknown { .. } => Region::new_var(root_vid),
        }
    }

    pub fn probe_value(
        &mut self,
        vid: RegionVid,
    ) -> Result<Region, UniverseIndex> {
        match self.unification_table_mut().probe_value(vid) {
            RegionVariableValue::Known { value } => Ok(value),
            RegionVariableValue::Unknown { universe } => Err(universe),
        }
    }

    fn combine_map(&mut self, t: CombineMapType) -> &mut CombineMap {
        match t {
            Glb => &mut self.storage.glbs,
            Lub => &mut self.storage.lubs,
        }
    }

    fn combine_vars(
        &mut self,
        cx: DbIr<'_>,
        t: CombineMapType,
        a: Region,
        b: Region,
        origin: SubregionOrigin,
    ) -> Region {
        let vars = TwoRegions { a: a.clone(), b: b.clone() };
        if let Some(c) = self.combine_map(t.clone()).get(&vars) {
            return Region::new_var(*c);
        }
        let a_universe = self.universe(a.clone());
        let b_universe = self.universe(b.clone());
        let c_universe = cmp::max(a_universe, b_universe);
        let c = self.new_region_var(c_universe, MiscVariable(origin.span()));
        self.combine_map(t.clone()).insert(vars.clone(), c);
        self.undo_log.push(AddCombination(t.clone(), vars));
        let new_r = Region::new_var(c);
        for old_r in [a, b] {
            match t {
                Glb => self.make_subregion(origin.clone(), new_r.clone(), old_r.clone()),
                Lub => self.make_subregion(origin.clone(), old_r, new_r.clone()),
            }
        }
        debug!("combine_vars() c={:?}", c);
        new_r
    }

    pub fn universe(&mut self, region: Region) -> UniverseIndex {
        match region.clone().kind() {
            RegionKind::ReStatic
            | RegionKind::ReErased
            | RegionKind::ReLateParam(..)
            | RegionKind::ReEarlyParam(..)
            | RegionKind::ReError(_) => UniverseIndex::ROOT,
            RegionKind::RePlaceholder(placeholder) => placeholder.universe,
            RegionKind::ReVar(vid) => match self.probe_value(vid) {
                Ok(value) => self.universe(value),
                Err(universe) => universe,
            },
            RegionKind::ReBound(..) => panic!("universe(): encountered bound region {:?}", region),
        }
    }

    pub fn vars_since_snapshot(
        &self,
        value_count: usize,
    ) -> (Range<RegionVid>, Vec<RegionVariableOrigin>) {
        let range =
            RegionVid::from(value_count)..RegionVid::from(self.storage.unification_table.len());
        (
            range.clone(),
            (range.start.index()..range.end.index())
                .map(|index| self.storage.var_infos[RegionVid::from(index)].origin.clone())
                .collect(),
        )
    }

    /// See `InferCtxt::region_constraints_added_in_snapshot`.
    pub fn region_constraints_added_in_snapshot(&self, mark: &Snapshot) -> bool {
        self.undo_log
            .region_constraints_in_snapshot(mark)
            .any(|elt| matches!(elt, AddConstraint(_)))
    }

    #[inline]
    fn unification_table_mut(&mut self) -> super::UnificationTable<'_, RegionVidKey> {
        ut::UnificationTable::with_log(&mut self.storage.unification_table, self.undo_log)
    }
}

impl fmt::Debug for RegionSnapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RegionSnapshot")
    }
}

impl fmt::Debug for GenericKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            GenericKind::Param(ref p) => write!(f, "{p:?}"),
            GenericKind::Placeholder(ref p) => write!(f, "{p:?}"),
            GenericKind::Alias(ref p) => write!(f, "{p:?}"),
        }
    }
}

impl fmt::Display for GenericKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            GenericKind::Param(ref p) => write!(f, "{p:?}"),
            GenericKind::Placeholder(ref p) => write!(f, "{p:?}"),
            GenericKind::Alias(ref p) => write!(f, "{p}"),
        }
    }
}

impl GenericKind {
    pub fn to_ty(&self, ir: DbIr<'_>) -> Ty {
        match *self {
            GenericKind::Param(ref p) => p.clone().to_ty(),
            GenericKind::Placeholder(ref p) => Ty::new_placeholder(p.clone()),
            GenericKind::Alias(ref p) => p.clone().to_ty(ir),
        }
    }
}

impl VerifyBound {
    pub fn must_hold(&self) -> bool {
        match self {
            VerifyBound::IfEq(..) => false,
            VerifyBound::OutlivedBy(re) => re.is_static(),
            VerifyBound::IsEmpty => false,
            VerifyBound::AnyBound(bs) => bs.iter().any(|b| b.must_hold()),
            VerifyBound::AllBounds(bs) => bs.iter().all(|b| b.must_hold()),
        }
    }

    pub fn cannot_hold(&self) -> bool {
        match self {
            VerifyBound::IfEq(..) => false,
            VerifyBound::IsEmpty => false,
            VerifyBound::OutlivedBy(_) => false,
            VerifyBound::AnyBound(bs) => bs.iter().all(|b| b.cannot_hold()),
            VerifyBound::AllBounds(bs) => bs.iter().any(|b| b.cannot_hold()),
        }
    }

    pub fn or(self, vb: VerifyBound) -> VerifyBound {
        if self.must_hold() || vb.cannot_hold() {
            self
        } else if self.cannot_hold() || vb.must_hold() {
            vb
        } else {
            VerifyBound::AnyBound(vec![self, vb])
        }
    }
}

impl RegionConstraintData {
    /// Returns `true` if this region constraint data contains no constraints, and `false`
    /// otherwise.
    pub fn is_empty(&self) -> bool {
        let RegionConstraintData { constraints, member_constraints, verifys } = self;
        constraints.is_empty() && member_constraints.is_empty() && verifys.is_empty()
    }
}

impl Rollback<UndoLog> for RegionConstraintStorage {
    fn reverse(&mut self, undo: UndoLog) {
        match undo {
            AddVar(vid) => {
                self.var_infos.pop().unwrap();
                assert_eq!(self.var_infos.len(), vid.index());
            }
            AddConstraint(index) => {
                self.data.constraints.pop().unwrap();
                assert_eq!(self.data.constraints.len(), index);
            }
            AddVerify(index) => {
                self.data.verifys.pop();
                assert_eq!(self.data.verifys.len(), index);
            }
            AddCombination(Glb, ref regions) => {
                self.glbs.remove(regions);
            }
            AddCombination(Lub, ref regions) => {
                self.lubs.remove(regions);
            }
        }
    }
}
