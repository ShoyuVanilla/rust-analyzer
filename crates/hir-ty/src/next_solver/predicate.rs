use std::cmp::Ordering;

use hir_def::GenericDefId;
use intern::Interned;
use rustc_ast_ir::try_visit;
use rustc_type_ir::{
    self as ty,
    elaborate::Elaboratable,
    error::{ExpectedFound, TypeError},
    fold::{TypeFoldable, TypeSuperFoldable},
    inherent::{IntoKind, SliceLike},
    relate::Relate,
    solve::Reveal,
    visit::{Flags, TypeSuperVisitable, TypeVisitable},
    CollectAndApply, DebruijnIndex, EarlyBinder, PredicatePolarity, TypeFlags, Upcast, UpcastFrom,
    WithCachedTypeInfo,
};
use smallvec::SmallVec;

use crate::interner::InternedWrapper;

use super::{flags::FlagComputation, interned_vec, Binder, BoundVarKinds, DbInterner, Region, Ty};

pub type BoundExistentialPredicate = Binder<ExistentialPredicate>;

pub type TraitRef = ty::TraitRef<DbInterner>;
pub type AliasTerm = ty::AliasTerm<DbInterner>;
pub type ProjectionPredicate = ty::ProjectionPredicate<DbInterner>;
pub type ExistentialPredicate = ty::ExistentialPredicate<DbInterner>;
pub type ExistentialTraitRef = ty::ExistentialTraitRef<DbInterner>;
pub type ExistentialProjection = ty::ExistentialProjection<DbInterner>;
pub type TraitPredicate = ty::TraitPredicate<DbInterner>;
pub type ClauseKind = ty::ClauseKind<DbInterner>;
pub type PredicateKind = ty::PredicateKind<DbInterner>;
pub type NormalizesTo = ty::NormalizesTo<DbInterner>;
pub type CoercePredicate = ty::CoercePredicate<DbInterner>;
pub type SubtypePredicate = ty::SubtypePredicate<DbInterner>;
pub type OutlivesPredicate<T> = ty::OutlivesPredicate<DbInterner, T>;
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;
pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;
pub type PolyTraitPredicate = Binder<TraitPredicate>;
pub type PolyRegionOutlivesPredicate = Binder<RegionOutlivesPredicate>;
pub type PolyTypeOutlivesPredicate = Binder<TypeOutlivesPredicate>;
pub type PolySubtypePredicate = Binder<SubtypePredicate>;
pub type PolyCoercePredicate = Binder<CoercePredicate>;
pub type PolyProjectionPredicate = Binder<ProjectionPredicate>;
pub type PolyTraitRef = Binder<TraitRef>;
pub type PolyExistentialTraitRef = Binder<ExistentialTraitRef>;
pub type PolyExistentialProjection = Binder<ExistentialProjection>;

/// Compares via an ordering that will not change if modules are reordered or other changes are
/// made to the tree. In particular, this ordering is preserved across incremental compilations.
fn stable_cmp_existential_predicate(
    a: &ExistentialPredicate,
    b: &ExistentialPredicate,
) -> Ordering {
    // FIXME: this is actual unstable - see impl in predicate.rs in `rustc_middle`
    match (a, b) {
        (ExistentialPredicate::Trait(_), ExistentialPredicate::Trait(_)) => Ordering::Equal,
        (ExistentialPredicate::Projection(ref a), ExistentialPredicate::Projection(ref b)) => {
            // Should sort by def path hash
            Ordering::Equal
        }
        (ExistentialPredicate::AutoTrait(ref a), ExistentialPredicate::AutoTrait(ref b)) => {
            // Should sort by def path hash
            Ordering::Equal
        }
        (ExistentialPredicate::Trait(_), _) => Ordering::Less,
        (ExistentialPredicate::Projection(_), ExistentialPredicate::Trait(_)) => Ordering::Greater,
        (ExistentialPredicate::Projection(_), _) => Ordering::Less,
        (ExistentialPredicate::AutoTrait(_), _) => Ordering::Greater,
    }
}
interned_vec!(BoundExistentialPredicates, BoundExistentialPredicate);

impl rustc_type_ir::inherent::BoundExistentialPredicates<DbInterner>
    for BoundExistentialPredicates
{
    fn principal_def_id(&self) -> Option<<DbInterner as rustc_type_ir::Interner>::DefId> {
        self.clone().principal().map(|trait_ref| trait_ref.skip_binder().def_id)
    }

    fn principal(
        self,
    ) -> Option<rustc_type_ir::Binder<DbInterner, rustc_type_ir::ExistentialTraitRef<DbInterner>>>
    {
        self.0 .0[0]
            .clone()
            .map_bound(|this| match this {
                ExistentialPredicate::Trait(tr) => Some(tr),
                _ => None,
            })
            .transpose()
    }

    fn auto_traits(
        self,
    ) -> impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::DefId> {
        self.iter().filter_map(|predicate| match predicate.skip_binder() {
            ExistentialPredicate::AutoTrait(did) => Some(did),
            _ => None,
        })
    }

    fn projection_bounds(
        self,
    ) -> impl IntoIterator<
        Item = rustc_type_ir::Binder<DbInterner, rustc_type_ir::ExistentialProjection<DbInterner>>,
    > {
        self.iter().filter_map(|predicate| {
            predicate
                .map_bound(|pred| match pred {
                    ExistentialPredicate::Projection(projection) => Some(projection),
                    _ => None,
                })
                .transpose()
        })
    }
}

impl rustc_type_ir::relate::Relate<DbInterner> for BoundExistentialPredicates {
    fn relate<R: rustc_type_ir::relate::TypeRelation<I = DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        // We need to perform this deduplication as we sometimes generate duplicate projections in `a`.
        let mut a_v: Vec<_> = a.clone().into_iter().collect();
        let mut b_v: Vec<_> = b.clone().into_iter().collect();
        // `skip_binder` here is okay because `stable_cmp` doesn't look at binders
        a_v.sort_by(|a, b| {
            stable_cmp_existential_predicate(a.as_ref().skip_binder(), b.as_ref().skip_binder())
        });
        a_v.dedup();
        b_v.sort_by(|a, b| {
            stable_cmp_existential_predicate(a.as_ref().skip_binder(), b.as_ref().skip_binder())
        });
        b_v.dedup();
        if a_v.len() != b_v.len() {
            return Err(TypeError::ExistentialMismatch(ExpectedFound::new(true, a, b)));
        }

        let v = std::iter::zip(a_v, b_v).map(|(ep_a, ep_b)| {
            match (ep_a.clone().skip_binder(), ep_b.clone().skip_binder()) {
                (ty::ExistentialPredicate::Trait(a), ty::ExistentialPredicate::Trait(b)) => {
                    Ok(ep_a.rebind(ty::ExistentialPredicate::Trait(
                        relation.relate(ep_a.rebind(a), ep_b.rebind(b))?.skip_binder(),
                    )))
                }
                (
                    ty::ExistentialPredicate::Projection(a),
                    ty::ExistentialPredicate::Projection(b),
                ) => Ok(ep_a.rebind(ty::ExistentialPredicate::Projection(
                    relation.relate(ep_a.rebind(a), ep_b.rebind(b))?.skip_binder(),
                ))),
                (
                    ty::ExistentialPredicate::AutoTrait(a),
                    ty::ExistentialPredicate::AutoTrait(b),
                ) if a == b => Ok(ep_a.rebind(ty::ExistentialPredicate::AutoTrait(a))),
                _ => Err(TypeError::ExistentialMismatch(ExpectedFound::new(
                    true,
                    a.clone(),
                    b.clone(),
                ))),
            }
        });

        CollectAndApply::collect_and_apply(v, |g| {
            BoundExistentialPredicates::new_from_iter(g.iter().cloned())
        })
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Predicate(Interned<InternedWrapper<WithCachedTypeInfo<Binder<PredicateKind>>>>);

impl std::fmt::Debug for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Binder<")?;
        match self.0 .0.internee.clone().skip_binder() {
            rustc_type_ir::PredicateKind::Clause(clause_kind) => {
                write!(f, "{:?}", clause_kind)
            }
            rustc_type_ir::PredicateKind::DynCompatible(trait_def_id) => {
                write!(f, "the trait `{:?}` is dyn-compatible", trait_def_id)
            }
            rustc_type_ir::PredicateKind::Subtype(subtype_predicate) => {
                write!(f, "{:?}", subtype_predicate)
            }
            rustc_type_ir::PredicateKind::Coerce(coerce_predicate) => {
                write!(f, "{:?}", coerce_predicate)
            }
            rustc_type_ir::PredicateKind::ConstEquate(c1, c2) => {
                write!(f, "the constant `{:?}` equals `{:?}`", c1, c2)
            }
            rustc_type_ir::PredicateKind::Ambiguous => write!(f, "ambiguous"),
            rustc_type_ir::PredicateKind::NormalizesTo(data) => write!(f, "{:?}", data),
            rustc_type_ir::PredicateKind::AliasRelate(t1, t2, dir) => {
                write!(f, "{:?} {:?} {:?}", t1, dir, t2)
            }
        }?;
        write!(f, ", [{:?}]>", self.0 .0.internee.bound_vars())?;
        Ok(())
    }
}

impl Predicate {
    pub fn new(kind: Binder<PredicateKind>) -> Self {
        let flags = FlagComputation::for_predicate(kind.clone());
        let cached = WithCachedTypeInfo {
            internee: kind,
            flags: flags.flags,
            outer_exclusive_binder: flags.outer_exclusive_binder,
        };
        Predicate(Interned::new(InternedWrapper(cached)))
    }

    /// Flips the polarity of a Predicate.
    ///
    /// Given `T: Trait` predicate it returns `T: !Trait` and given `T: !Trait` returns `T: Trait`.
    pub fn flip_polarity(self) -> Option<Predicate> {
        let kind = self
            .kind()
            .map_bound(|kind| match kind {
                PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                    trait_ref,
                    polarity,
                })) => Some(PredicateKind::Clause(ClauseKind::Trait(TraitPredicate {
                    trait_ref,
                    polarity: polarity.flip(),
                }))),

                _ => None,
            })
            .transpose()?;

        Some(Predicate::new(kind))
    }
}

// FIXME: should make a "header" in interned_vec

#[derive(Debug)]
pub struct InternedClausesWrapper(SmallVec<[Clause; 2]>, TypeFlags, DebruijnIndex);

impl PartialEq for InternedClausesWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for InternedClausesWrapper {}

impl std::hash::Hash for InternedClausesWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

type InternedClauses = Interned<InternedClausesWrapper>;

#[derive(Debug, Clone)]
pub struct Clauses(InternedClauses);

impl Clauses {
    pub fn new_from_iter(data: impl IntoIterator<Item = Clause>) -> Self {
        let clauses: SmallVec<_> = data.into_iter().collect();
        let flags = FlagComputation::for_clauses(&clauses);
        let wrapper = InternedClausesWrapper(clauses, flags.flags, flags.outer_exclusive_binder);
        Clauses(Interned::new(wrapper))
    }
}

impl PartialEq for Clauses {
    fn eq(&self, other: &Self) -> bool {
        self.0 .0.eq(&other.0 .0)
    }
}

impl Eq for Clauses {}

impl std::hash::Hash for Clauses {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0 .0.hash(state)
    }
}

impl rustc_type_ir::inherent::SliceLike for Clauses {
    type Item = Clause;

    type IntoIter = <SmallVec<[Clause; 2]> as IntoIterator>::IntoIter;

    fn iter(self) -> Self::IntoIter {
        self.0 .0.clone().into_iter()
    }

    fn as_slice(&self) -> &[Self::Item] {
        self.0 .0.as_slice()
    }
}

impl IntoIterator for Clauses {
    type Item = Clause;
    type IntoIter = <Self as rustc_type_ir::inherent::SliceLike>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        rustc_type_ir::inherent::SliceLike::iter(self)
    }
}

impl Default for Clauses {
    fn default() -> Self {
        Clauses::new_from_iter([])
    }
}

impl rustc_type_ir::fold::TypeFoldable<DbInterner> for Clauses {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        use rustc_type_ir::inherent::SliceLike as _;
        Ok(Clauses::new_from_iter(
            self.iter()
                .map(|v| v.try_fold_with(folder))
                .collect::<Result<SmallVec<[_; 2]>, _>>()?,
        ))
    }
}

impl rustc_type_ir::visit::TypeVisitable<DbInterner> for Clauses {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        use rustc_ast_ir::visit::VisitorResult;
        use rustc_type_ir::inherent::SliceLike as _;
        rustc_ast_ir::walk_visitable_list!(visitor, self.as_slice().iter());
        V::Result::output()
    }
}

impl rustc_type_ir::visit::Flags for Clauses {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.0 .1
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.0 .2
    }
}

impl rustc_type_ir::visit::TypeSuperVisitable<DbInterner> for Clauses {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        self.as_slice().visit_with(visitor)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)] // TODO implement Debug by hand
pub struct Clause(pub(crate) Predicate);

// We could cram the reveal into the clauses like rustc does, probably
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ParamEnv {
    pub(crate) reveal: Reveal,
    pub(crate) clauses: Clauses,
}

impl ParamEnv {
    pub fn empty() -> Self {
        ParamEnv { reveal: Reveal::UserFacing, clauses: Clauses::new_from_iter([]) }
    }
}

impl TypeVisitable<DbInterner> for ParamEnv {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        try_visit!(self.clauses.visit_with(visitor));
        self.reveal.visit_with(visitor)
    }
}

impl TypeFoldable<DbInterner> for ParamEnv {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(ParamEnv {
            reveal: self.reveal.try_fold_with(folder)?,
            clauses: self.clauses.try_fold_with(folder)?,
        })
    }
}

impl rustc_type_ir::inherent::ParamEnv<DbInterner> for ParamEnv {
    fn reveal(&self) -> rustc_type_ir::solve::Reveal {
        self.reveal
    }

    fn caller_bounds(
        self,
    ) -> impl IntoIterator<Item = <DbInterner as rustc_type_ir::Interner>::Clause> {
        self.clauses.iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParamEnvAnd<T> {
    pub param_env: ParamEnv,
    pub value: T,
}

impl<T> ParamEnvAnd<T> {
    pub fn into_parts(self) -> (ParamEnv, T) {
        (self.param_env, self.value)
    }
}

impl TypeVisitable<DbInterner> for Predicate {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_predicate(self.clone())
    }
}

impl TypeSuperVisitable<DbInterner> for Predicate {
    fn super_visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        self.clone().kind().visit_with(visitor)
    }
}

impl TypeFoldable<DbInterner> for Predicate {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_predicate(self)
    }
}

impl TypeSuperFoldable<DbInterner> for Predicate {
    fn try_super_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        let new = self.kind().try_fold_with(folder)?;
        Ok(Predicate::new(new))
    }
}

impl Elaboratable<DbInterner> for Predicate {
    fn predicate_kind(
        self,
    ) -> rustc_type_ir::Binder<DbInterner, rustc_type_ir::PredicateKind<DbInterner>> {
        self.0 .0.internee.clone()
    }

    fn as_clause(self) -> Option<<DbInterner as rustc_type_ir::Interner>::Clause> {
        match self.0 .0.internee.as_ref().skip_binder() {
            PredicateKind::Clause(..) => Some(Clause(self)),
            _ => None,
        }
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        clause.as_predicate()
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        _span: <DbInterner as rustc_type_ir::Interner>::Span,
        _parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        _index: usize,
    ) -> Self {
        clause.as_predicate()
    }
}

impl Flags for Predicate {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.0 .0.flags
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        self.0 .0.outer_exclusive_binder
    }
}

impl IntoKind for Predicate {
    type Kind = Binder<PredicateKind>;

    fn kind(self) -> Self::Kind {
        self.0 .0.internee.clone()
    }
}

impl UpcastFrom<DbInterner, ty::PredicateKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::PredicateKind<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::PredicateKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Predicate::new(from)
    }
}
impl UpcastFrom<DbInterner, ty::ClauseKind<DbInterner>> for Predicate {
    fn upcast_from(from: ty::ClauseKind<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(PredicateKind::Clause(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        from.map_bound(PredicateKind::Clause).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Clause> for Predicate {
    fn upcast_from(from: Clause, _interner: DbInterner) -> Self {
        from.0
    }
}
impl UpcastFrom<DbInterner, ty::NormalizesTo<DbInterner>> for Predicate {
    fn upcast_from(from: ty::NormalizesTo<DbInterner>, interner: DbInterner) -> Self {
        PredicateKind::NormalizesTo(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        Binder::dummy(from).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Predicate {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        from.map_bound(|trait_ref| TraitPredicate {
            trait_ref,
            polarity: PredicatePolarity::Positive,
        })
        .upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Binder<ty::TraitPredicate<DbInterner>>> for Predicate {
    fn upcast_from(from: Binder<ty::TraitPredicate<DbInterner>>, interner: DbInterner) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Trait(it))).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, Binder<ProjectionPredicate>> for Predicate {
    fn upcast_from(from: Binder<ProjectionPredicate>, interner: DbInterner) -> Self {
        from.map_bound(|it| PredicateKind::Clause(ClauseKind::Projection(it))).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ProjectionPredicate> for Predicate {
    fn upcast_from(from: ProjectionPredicate, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::Projection(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Predicate {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::Trait(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Ty>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Ty>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::TypeOutlives(from)).upcast(interner)
    }
}
impl UpcastFrom<DbInterner, ty::OutlivesPredicate<DbInterner, Region>> for Predicate {
    fn upcast_from(from: ty::OutlivesPredicate<DbInterner, Region>, interner: DbInterner) -> Self {
        PredicateKind::Clause(ClauseKind::RegionOutlives(from)).upcast(interner)
    }
}

impl rustc_type_ir::inherent::Predicate<DbInterner> for Predicate {
    fn as_clause(self) -> Option<<DbInterner as rustc_type_ir::Interner>::Clause> {
        match self.clone().kind().skip_binder() {
            PredicateKind::Clause(..) => Some(self.expect_clause()),
            _ => None,
        }
    }

    fn is_coinductive(&self, interner: DbInterner) -> bool {
        match self.clone().kind().skip_binder() {
            ty::PredicateKind::Clause(ty::ClauseKind::Trait(data)) => {
                // FIXME
                /*
                let trait_ = match trait_def_id {
                    GenericDefId::TraitId(id) => id,
                    _ => panic!("Unexpected GenericDefId in trait_is_auto"),
                };
                let trait_data = self.db.trait_data(trait_);
                trait_data.is_auto
                */
                false
            }
            ty::PredicateKind::Clause(ty::ClauseKind::WellFormed(_)) => true,
            _ => false,
        }
    }

    /// Whether this projection can be soundly normalized.
    ///
    /// Wf predicates must not be normalized, as normalization
    /// can remove required bounds which would cause us to
    /// unsoundly accept some programs. See #91068.
    fn allow_normalization(&self) -> bool {
        // TODO: this should probably live in rustc_type_ir
        match self.0 .0.as_ref().skip_binder() {
            PredicateKind::Clause(ClauseKind::WellFormed(_))
            | PredicateKind::AliasRelate(..)
            | PredicateKind::NormalizesTo(..) => false,
            PredicateKind::Clause(ClauseKind::Trait(_))
            | PredicateKind::Clause(ClauseKind::RegionOutlives(_))
            | PredicateKind::Clause(ClauseKind::TypeOutlives(_))
            | PredicateKind::Clause(ClauseKind::Projection(_))
            | PredicateKind::Clause(ClauseKind::ConstArgHasType(..))
            | PredicateKind::Clause(ClauseKind::HostEffect(..))
            | PredicateKind::DynCompatible(_)
            | PredicateKind::Subtype(_)
            | PredicateKind::Coerce(_)
            | PredicateKind::Clause(ClauseKind::ConstEvaluatable(_))
            | PredicateKind::ConstEquate(_, _)
            | PredicateKind::Ambiguous => true,
        }
    }
}

impl Predicate {
    /// Assert that the predicate is a clause.
    pub fn expect_clause(self) -> Clause {
        match self.clone().kind().skip_binder() {
            PredicateKind::Clause(..) => Clause(self.clone()),
            _ => panic!("{self:?} is not a clause"),
        }
    }
}

impl TypeVisitable<DbInterner> for Clause {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_predicate(self.clone().as_predicate())
    }
}

impl TypeFoldable<DbInterner> for Clause {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(folder.try_fold_predicate(self.clone().as_predicate())?.expect_clause())
    }
}

impl IntoKind for Clause {
    type Kind = Binder<ClauseKind>;

    fn kind(self) -> Self::Kind {
        self.0.kind().map_bound(|pk| match pk {
            PredicateKind::Clause(kind) => kind,
            _ => unreachable!(),
        })
    }
}

impl Clause {
    pub fn as_predicate(self) -> Predicate {
        self.0
    }
}

impl Elaboratable<DbInterner> for Clause {
    fn predicate_kind(
        self,
    ) -> rustc_type_ir::Binder<DbInterner, rustc_type_ir::PredicateKind<DbInterner>> {
        self.as_predicate().kind()
    }

    fn as_clause(self) -> Option<<DbInterner as rustc_type_ir::Interner>::Clause> {
        Some(self)
    }

    fn child(&self, clause: <DbInterner as rustc_type_ir::Interner>::Clause) -> Self {
        clause
    }

    fn child_with_derived_cause(
        &self,
        clause: <DbInterner as rustc_type_ir::Interner>::Clause,
        _span: <DbInterner as rustc_type_ir::Interner>::Span,
        _parent_trait_pred: rustc_type_ir::Binder<
            DbInterner,
            rustc_type_ir::TraitPredicate<DbInterner>,
        >,
        _index: usize,
    ) -> Self {
        clause
    }
}

impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ClauseKind<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.map_bound(PredicateKind::Clause).upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::TraitRef<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitRef<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitRef<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitRef<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::TraitPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::TraitPredicate<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>> for Clause {
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::TraitPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::ProjectionPredicate<DbInterner>> for Clause {
    fn upcast_from(from: ty::ProjectionPredicate<DbInterner>, interner: DbInterner) -> Self {
        Clause(from.upcast(interner))
    }
}
impl UpcastFrom<DbInterner, ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>>
    for Clause
{
    fn upcast_from(
        from: ty::Binder<DbInterner, ty::ProjectionPredicate<DbInterner>>,
        interner: DbInterner,
    ) -> Self {
        Clause(from.upcast(interner))
    }
}

impl rustc_type_ir::inherent::Clause<DbInterner> for Clause {
    fn as_predicate(self) -> <DbInterner as rustc_type_ir::Interner>::Predicate {
        self.0
    }

    fn instantiate_supertrait(
        self,
        cx: DbInterner,
        trait_ref: rustc_type_ir::Binder<DbInterner, rustc_type_ir::TraitRef<DbInterner>>,
    ) -> Self {
        // See the rustc impl for a long comment
        let bound_pred = self.kind();
        let pred_bound_vars = bound_pred.bound_vars();
        let trait_bound_vars = trait_ref.bound_vars();
        // 1) Self: Bar1<'a, '^0.0> -> Self: Bar1<'a, '^0.1>
        let shifted_pred =
            cx.shift_bound_var_indices(trait_bound_vars.len(), bound_pred.skip_binder());
        // 2) Self: Bar1<'a, '^0.1> -> T: Bar1<'^0.0, '^0.1>
        let new = EarlyBinder::bind(shifted_pred).instantiate(cx, trait_ref.skip_binder().args);
        // 3) ['x] + ['b] -> ['x, 'b]
        let bound_vars =
            BoundVarKinds::new_from_iter(trait_bound_vars.iter().chain(pred_bound_vars.iter()));

        // FIXME: Is it really perf sensitive to use reuse_or_mk_predicate here?
        let predicate: Predicate =
            ty::Binder::bind_with_vars(PredicateKind::Clause(new), bound_vars).upcast(cx);
        predicate.expect_clause()
    }
}
