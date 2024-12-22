use hir_def::{db::DefDatabase, generics::TypeOrConstParamData, GenericDefId, GenericParamId};
use hir_expand::name::Name;
use intern::Symbol;

use crate::{db::HirDatabase, generics::parent_generic_def, next_solver::Ty};

use super::{Const, EarlyParamRegion, ParamConst, Region};

use super::{DbInterner, GenericArg};

pub(crate) fn generics(db: &dyn DefDatabase, def: GenericDefId) -> Generics {
    let parent = parent_generic_def(db, def);
    let parent_generics = parent.map(|def| Box::new(generics(db, def)));
    let params = db.generic_params(def);

    let own_params = params
        .iter_lt()
        .enumerate()
        .map(|(index, (_, lt))| {
            let name = lt.name.symbol().clone();
            let index = index as u32;
            let kind = GenericParamDefKind::Lifetime;
            GenericParamDef { name, index, kind }
        })
        .chain(params.iter_type_or_consts().enumerate().map(|(index, (_, p))| {
            let name = p
                .name()
                .map(|n| n.symbol().clone())
                .unwrap_or_else(|| Name::missing().symbol().clone());
            let index = (params.len_lifetimes() + index) as u32;
            let kind = match p {
                TypeOrConstParamData::TypeParamData(_) => GenericParamDefKind::Type,
                TypeOrConstParamData::ConstParamData(_) => GenericParamDefKind::Const,
            };
            GenericParamDef { name, index, kind }
        }))
        .collect();

    Generics {
        parent,
        parent_count: parent_generics.map_or(0, |g| g.parent_count + g.own_params.len()),
        own_params,
    }
}

#[derive(Debug)]
pub struct Generics {
    pub parent: Option<GenericDefId>,
    pub parent_count: usize,
    pub own_params: Vec<GenericParamDef>,
}

#[derive(Debug)]
pub struct GenericParamDef {
    pub(crate) name: Symbol,
    //def_id: GenericDefId,
    index: u32,
    pub(crate) kind: GenericParamDefKind,
}

impl GenericParamDef {
    pub fn index(&self) -> u32 {
        self.index
    }
}

#[derive(Debug)]
pub enum GenericParamDefKind {
    Lifetime,
    Type,
    Const,
}

impl rustc_type_ir::inherent::GenericsOf<DbInterner> for Generics {
    fn count(&self) -> usize {
        self.parent_count + self.own_params.len()
    }
}

impl GenericParamDef {
    pub fn to_error(&self, interner: DbInterner) -> GenericArg {
        match &self.kind {
            GenericParamDefKind::Lifetime => Region::error().into(),
            GenericParamDefKind::Type => Ty::error().into(),
            GenericParamDefKind::Const => Const::error().into(),
        }
    }
}

impl DbInterner {
    pub fn mk_param_from_def(self, param: &GenericParamDef) -> GenericArg {
        match param.kind {
            GenericParamDefKind::Lifetime => Region::new_early_param(EarlyParamRegion {
                index: param.index,
                name: param.name.clone(),
            })
            .into(),
            GenericParamDefKind::Type => Ty::new_param(param.index, param.name.clone()).into(),
            GenericParamDefKind::Const => {
                Const::new_param(ParamConst { index: param.index, name: param.name.clone() }).into()
            }
        }
    }
}
