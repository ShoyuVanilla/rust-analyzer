use hir_def::GenericDefId;
use intern::{Interned, Symbol};
use rustc_type_ir::{
    fold::TypeFoldable,
    inherent::{IntoKind, PlaceholderLike},
    relate::Relate,
    visit::{Flags, TypeVisitable},
    BoundVar, RegionVid, TypeFlags, INNERMOST,
};

use crate::interner::InternedWrapper;

use super::{
    interner::{BoundVarKind, DbInterner, Placeholder},
    ErrorGuaranteed,
};

type RegionKind = rustc_type_ir::RegionKind<DbInterner>;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Region(Interned<InternedWrapper<RegionKind>>);

impl Region {
    pub fn new(kind: RegionKind) -> Self {
        Region(Interned::new(InternedWrapper(kind)))
    }

    pub fn new_early_param(early_bound_region: EarlyParamRegion) -> Self {
        Region::new(RegionKind::ReEarlyParam(early_bound_region))
    }

    pub fn new_placeholder(placeholder: PlaceholderRegion) -> Self {
        Region::new(RegionKind::RePlaceholder(placeholder))
    }

    pub fn new_var(v: RegionVid) -> Region {
        Region::new(RegionKind::ReVar(v))
    }

    pub fn is_placeholder(&self) -> bool {
        matches!(self.0 .0, RegionKind::RePlaceholder(..))
    }

    pub fn is_static(&self) -> bool {
        matches!(self.0 .0, RegionKind::ReStatic)
    }
}

pub type PlaceholderRegion = Placeholder<BoundRegion>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct EarlyParamRegion {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug manually
/// The parameter representation of late-bound function parameters, "some region
/// at least as big as the scope `fr.scope`".
///
/// Similar to a placeholder region as we create `LateParam` regions when entering a binder
/// except they are always in the root universe and instead of using a boundvar to distinguish
/// between others we use the `DefId` of the parameter. For this reason the `bound_region` field
/// should basically always be `BoundRegionKind::Named` as otherwise there is no way of telling
/// different parameters apart.
pub struct LateParamRegion {
    pub scope: GenericDefId,
    pub bound_region: BoundRegionKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)] // FIXME implement Debug manually
pub enum BoundRegionKind {
    /// An anonymous region parameter for a given fn (&T)
    Anon,

    /// Named region parameters for functions (a in &'a T)
    ///
    /// The `DefId` is needed to distinguish free regions in
    /// the event of shadowing.
    Named(GenericDefId, Symbol),

    /// Anonymous region for the implicit env pointer parameter
    /// to a closure
    ClosureEnv,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl rustc_type_ir::inherent::ParamLike for EarlyParamRegion {
    fn index(&self) -> u32 {
        self.index
    }
}

impl std::fmt::Debug for EarlyParamRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.index)
        // write!(f, "{}/#{}", self.name, self.index)
    }
}

impl rustc_type_ir::inherent::BoundVarLike<DbInterner> for BoundRegion {
    fn var(&self) -> BoundVar {
        self.var
    }

    fn assert_eq(self, var: BoundVarKind) {
        assert_eq!(self.kind, var.expect_region())
    }
}

impl core::fmt::Debug for BoundRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            BoundRegionKind::Anon => write!(f, "{:?}", self.var),
            BoundRegionKind::ClosureEnv => write!(f, "{:?}.Env", self.var),
            BoundRegionKind::Named(def, symbol) => {
                write!(f, "{:?}.Named({:?}, {:?})", self.var, def, symbol)
            }
        }
    }
}

impl BoundRegionKind {
    pub fn is_named(&self) -> bool {
        match self {
            BoundRegionKind::Named(_, name) => {
                true
                // name != kw::UnderscoreLifetime && name != kw::Empty
            }
            _ => false,
        }
    }

    pub fn get_name(&self) -> Option<Symbol> {
        if self.is_named() {
            match self {
                BoundRegionKind::Named(_, name) => return Some(name.clone()),
                _ => unreachable!(),
            }
        }

        None
    }

    pub fn get_id(&self) -> Option<GenericDefId> {
        match self {
            BoundRegionKind::Named(id, _) => Some(*id),
            _ => None,
        }
    }
}

impl IntoKind for Region {
    type Kind = RegionKind;

    fn kind(self) -> Self::Kind {
        self.0 .0.clone()
    }
}

impl TypeVisitable<DbInterner> for Region {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<DbInterner>>(
        &self,
        visitor: &mut V,
    ) -> V::Result {
        visitor.visit_region(self.clone())
    }
}

impl TypeFoldable<DbInterner> for Region {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<DbInterner>>(
        self,
        folder: &mut F,
    ) -> Result<Self, F::Error> {
        folder.try_fold_region(self)
    }
}

impl Relate<DbInterner> for Region {
    fn relate<R: rustc_type_ir::relate::TypeRelation<I = DbInterner>>(
        relation: &mut R,
        a: Self,
        b: Self,
    ) -> rustc_type_ir::relate::RelateResult<DbInterner, Self> {
        relation.regions(a, b)
    }
}

impl Flags for Region {
    fn flags(&self) -> rustc_type_ir::TypeFlags {
        self.type_flags()
    }

    fn outer_exclusive_binder(&self) -> rustc_type_ir::DebruijnIndex {
        match &self.0 .0 {
            RegionKind::ReBound(debruijn, _) => debruijn.shifted_in(1),
            _ => INNERMOST,
        }
    }
}

impl rustc_type_ir::inherent::Region<DbInterner> for Region {
    fn new_bound(
        _interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: BoundRegion,
    ) -> Self {
        Region::new(RegionKind::ReBound(debruijn, var))
    }

    fn new_anon_bound(
        _interner: DbInterner,
        debruijn: rustc_type_ir::DebruijnIndex,
        var: rustc_type_ir::BoundVar,
    ) -> Self {
        Region::new(RegionKind::ReBound(debruijn, BoundRegion { var, kind: BoundRegionKind::Anon }))
    }

    fn new_static(_interner: DbInterner) -> Self {
        Region::new(RegionKind::ReStatic)
    }
}

impl Region {
    pub fn error() -> Self {
        Region::new(RegionKind::ReError(ErrorGuaranteed))
    }

    pub fn type_flags(&self) -> TypeFlags {
        let mut flags = TypeFlags::empty();

        match &self.0 .0 {
            RegionKind::ReVar(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_INFER;
            }
            RegionKind::RePlaceholder(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_PLACEHOLDER;
            }
            RegionKind::ReEarlyParam(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
                flags |= TypeFlags::HAS_RE_PARAM;
            }
            RegionKind::ReLateParam(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_FREE_LOCAL_REGIONS;
            }
            RegionKind::ReStatic => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
            }
            RegionKind::ReBound(..) => {
                flags |= TypeFlags::HAS_RE_BOUND;
            }
            RegionKind::ReErased => {
                flags |= TypeFlags::HAS_RE_ERASED;
            }
            RegionKind::ReError(..) => {
                flags |= TypeFlags::HAS_FREE_REGIONS;
                flags |= TypeFlags::HAS_ERROR;
            }
        }

        flags
    }
}

impl PlaceholderLike for PlaceholderRegion {
    fn universe(&self) -> rustc_type_ir::UniverseIndex {
        self.universe
    }

    fn var(&self) -> rustc_type_ir::BoundVar {
        self.bound.var
    }

    fn with_updated_universe(&self, ui: rustc_type_ir::UniverseIndex) -> Self {
        Placeholder { universe: ui, bound: self.bound.clone() }
    }

    fn new(ui: rustc_type_ir::UniverseIndex, var: rustc_type_ir::BoundVar) -> Self {
        Placeholder { universe: ui, bound: BoundRegion { var, kind: BoundRegionKind::Anon } }
    }
}
