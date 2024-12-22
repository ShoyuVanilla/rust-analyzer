//! This module contains the definitions of most `TypeRelation`s in the type system
//! (except for some relations used for diagnostics and heuristics in the compiler).
//! As well as the implementation of `Relate` for interned things (`Ty`/`Const`/etc).

pub use rustc_type_ir::relate::combine::PredicateEmittingRelation;
pub use rustc_type_ir::relate::*;

use crate::next_solver::DbInterner;

mod generalize;
mod higher_ranked;
pub(super) mod lattice;

pub type RelateResult<T> = rustc_type_ir::relate::RelateResult<DbInterner, T>;
