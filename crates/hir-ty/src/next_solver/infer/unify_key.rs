use std::cmp;
use std::marker::PhantomData;

use ena::unify::{NoError, UnifyKey, UnifyValue};
use hir_def::GenericDefId;
use rustc_type_ir::{inherent::IntoKind, ConstVid, RegionKind, RegionVid, UniverseIndex};

use crate::next_solver::{Const, DbIr, Region, Span, Ty};

pub trait ToType {
    fn to_type(&self, cx: DbIr<'_>) -> Ty;
}

#[derive(Clone, Debug)]
pub enum RegionVariableValue {
    Known { value: Region },
    Unknown { universe: UniverseIndex },
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub struct RegionVidKey {
    pub vid: RegionVid,
    pub phantom: PhantomData<RegionVariableValue>,
}

impl From<RegionVid> for RegionVidKey {
    fn from(vid: RegionVid) -> Self {
        RegionVidKey { vid, phantom: PhantomData }
    }
}

impl UnifyKey for RegionVidKey {
    type Value = RegionVariableValue;
    #[inline]
    fn index(&self) -> u32 {
        self.vid.as_u32()
    }
    #[inline]
    fn from_index(i: u32) -> Self {
        RegionVidKey::from(RegionVid::from_u32(i))
    }
    fn tag() -> &'static str {
        "RegionVidKey"
    }
}

pub struct RegionUnificationError;
impl UnifyValue for RegionVariableValue {
    type Error = RegionUnificationError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (value1, value2) {
            (RegionVariableValue::Known { .. }, RegionVariableValue::Known { .. }) => {
                Err(RegionUnificationError)
            }

            (RegionVariableValue::Known { value }, RegionVariableValue::Unknown { universe })
            | (RegionVariableValue::Unknown { universe }, RegionVariableValue::Known { value }) => {
                let universe_of_value = match value.clone().kind() {
                    RegionKind::ReStatic
                    | RegionKind::ReErased
                    | RegionKind::ReLateParam(..)
                    | RegionKind::ReEarlyParam(..)
                    | RegionKind::ReError(_) => UniverseIndex::ROOT,
                    RegionKind::RePlaceholder(placeholder) => placeholder.universe,
                    RegionKind::ReVar(..) | RegionKind::ReBound(..) => panic!("not a universal region"),
                };

                if universe.can_name(universe_of_value) {
                    Ok(RegionVariableValue::Known { value: value.clone() })
                } else {
                    Err(RegionUnificationError)
                }
            }

            (
                RegionVariableValue::Unknown { universe: a },
                RegionVariableValue::Unknown { universe: b },
            ) => {
                // If we unify two unconstrained regions then whatever
                // value they wind up taking (which must be the same value) must
                // be nameable by both universes. Therefore, the resulting
                // universe is the minimum of the two universes, because that is
                // the one which contains the fewest names in scope.
                Ok(RegionVariableValue::Unknown { universe: (*a).min(*b) })
            }
        }
    }
}

// Generic consts.

#[derive(Copy, Clone, Debug)]
pub struct ConstVariableOrigin {
    pub span: Span,
    /// `DefId` of the const parameter this was instantiated for, if any.
    ///
    /// This should only be used for diagnostics.
    pub param_def_id: Option<GenericDefId>,
}

#[derive(Clone, Debug)]
pub enum ConstVariableValue {
    Known { value: Const },
    Unknown { origin: ConstVariableOrigin, universe: UniverseIndex },
}

impl ConstVariableValue {
    /// If this value is known, returns the const it is known to be.
    /// Otherwise, `None`.
    pub fn known(&self) -> Option<Const> {
        match self {
            ConstVariableValue::Unknown { .. } => None,
            ConstVariableValue::Known { value } => Some(value.clone()),
        }
    }
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub struct ConstVidKey {
    pub vid: ConstVid,
    pub phantom: PhantomData<Const>,
}

impl From<ConstVid> for ConstVidKey {
    fn from(vid: ConstVid) -> Self {
        ConstVidKey { vid, phantom: PhantomData }
    }
}

impl UnifyKey for ConstVidKey {
    type Value = ConstVariableValue;
    #[inline]
    fn index(&self) -> u32 {
        self.vid.as_u32()
    }
    #[inline]
    fn from_index(i: u32) -> Self {
        ConstVidKey::from(ConstVid::from_u32(i))
    }
    fn tag() -> &'static str {
        "ConstVidKey"
    }
}

impl UnifyValue for ConstVariableValue {
    type Error = NoError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, Self::Error> {
        match (value1, value2) {
            (ConstVariableValue::Known { .. }, ConstVariableValue::Known { .. }) => {
                panic!("equating two const variables, both of which have known values")
            }

            // If one side is known, prefer that one.
            (ConstVariableValue::Known { .. }, ConstVariableValue::Unknown { .. }) => Ok(value1.clone()),
            (ConstVariableValue::Unknown { .. }, ConstVariableValue::Known { .. }) => Ok(value2.clone()),

            // If both sides are *unknown*, it hardly matters, does it?
            (
                ConstVariableValue::Unknown { origin, universe: universe1 },
                ConstVariableValue::Unknown { origin: _, universe: universe2 },
            ) => {
                // If we unify two unbound variables, ?T and ?U, then whatever
                // value they wind up taking (which must be the same value) must
                // be nameable by both universes. Therefore, the resulting
                // universe is the minimum of the two universes, because that is
                // the one which contains the fewest names in scope.
                let universe = cmp::min(*universe1, *universe2);
                Ok(ConstVariableValue::Unknown { origin: *origin, universe })
            }
        }
    }
}
