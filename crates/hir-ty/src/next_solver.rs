#![allow(unused, unreachable_pub)]

pub mod abi;
mod consts;
mod flags;
pub mod fold;
mod generic_arg;
pub mod generics;
pub mod infer;
//mod infer_new;
pub mod interner;
mod ir_print;
pub mod mapping;
mod opaques;
pub mod predicate;
mod region;
mod solver;
mod ty;
pub mod util;
pub mod walk;

pub use consts::*;
pub use generic_arg::*;
//pub use infer_new::*;
pub use interner::*;
pub use opaques::*;
pub use predicate::*;
pub use region::*;
pub use solver::*;
pub use ty::*;

pub type Binder<T> = rustc_type_ir::Binder<DbInterner, T>;
pub type EarlyBinder<T> = rustc_type_ir::EarlyBinder<DbInterner, T>;
pub type Canonical<T> = rustc_type_ir::Canonical<DbInterner, T>;
pub type CanonicalVarValues = rustc_type_ir::CanonicalVarValues<DbInterner>;
pub type CanonicalVarInfo = rustc_type_ir::CanonicalVarInfo<DbInterner>;
pub type CanonicalQueryInput<V> = rustc_type_ir::CanonicalQueryInput<DbInterner, V>;
pub type AliasTy = rustc_type_ir::AliasTy<DbInterner>;
pub type PolyFnSig = Binder<rustc_type_ir::FnSig<DbInterner>>;
pub type TypingMode = rustc_type_ir::TypingMode<DbInterner>;

pub type FxIndexMap<K, V> =
    indexmap::IndexMap<K, V, std::hash::BuildHasherDefault<rustc_hash::FxHasher>>;
