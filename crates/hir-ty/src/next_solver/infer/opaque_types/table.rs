use ena::undo_log::UndoLogs;
use tracing::instrument;

use super::{OpaqueHiddenType, OpaqueTypeDecl, OpaqueTypeMap};
use crate::next_solver::{
    infer::snapshot::undo_log::{InferCtxtUndoLogs, UndoLog},
    OpaqueTypeKey, Ty,
};

#[derive(Default, Debug, Clone)]
pub(crate) struct OpaqueTypeStorage {
    /// Opaque types found in explicit return types and their
    /// associated fresh inference variable. Writeback resolves these
    /// variables to get the concrete type, which can be used to
    /// 'de-opaque' OpaqueTypeDecl, after typeck is done with all functions.
    pub opaque_types: OpaqueTypeMap,
}

impl OpaqueTypeStorage {
    #[instrument(level = "debug")]
    pub(crate) fn remove(&mut self, key: OpaqueTypeKey, idx: Option<OpaqueHiddenType>) {
        if let Some(idx) = idx {
            self.opaque_types.get_mut(&key).unwrap().hidden_type = idx;
        } else {
            // FIXME(#120456) - is `swap_remove` correct?
            match self.opaque_types.swap_remove(&key) {
                None => {
                    panic!("reverted opaque type inference that was never registered: {:?}", key)
                }
                Some(_) => {}
            }
        }
    }

    #[inline]
    pub(crate) fn with_log<'a>(
        &'a mut self,
        undo_log: &'a mut InferCtxtUndoLogs,
    ) -> OpaqueTypeTable<'a> {
        OpaqueTypeTable { storage: self, undo_log }
    }
}

impl Drop for OpaqueTypeStorage {
    fn drop(&mut self) {
        if !self.opaque_types.is_empty() {
            panic!("{:?}", self.opaque_types)
        }
    }
}

pub(crate) struct OpaqueTypeTable<'a> {
    storage: &'a mut OpaqueTypeStorage,

    undo_log: &'a mut InferCtxtUndoLogs,
}

impl OpaqueTypeTable<'_> {
    #[instrument(skip(self), level = "debug")]
    pub(crate) fn register(
        &mut self,
        key: OpaqueTypeKey,
        hidden_type: OpaqueHiddenType,
    ) -> Option<Ty> {
        if let Some(decl) = self.storage.opaque_types.get_mut(&key) {
            let prev = std::mem::replace(&mut decl.hidden_type, hidden_type);
            self.undo_log.push(UndoLog::OpaqueTypes(key, Some(prev.clone())));
            return Some(prev.ty);
        }
        let decl = OpaqueTypeDecl { hidden_type };
        self.storage.opaque_types.insert(key.clone(), decl);
        self.undo_log.push(UndoLog::OpaqueTypes(key, None));
        None
    }
}
