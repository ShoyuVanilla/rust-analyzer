use chalk_ir::{DebruijnIndex, WhereClause};
use hir_def::{
    lang_item::LangItem, AssocItemId, ConstId, FunctionId, GenericDefId, HasModule, TraitId,
    TypeAliasId,
};

use crate::{
    all_super_traits, db::HirDatabase, generics::generics, layout::LayoutError,
    lower::callable_item_sig, make_single_type_binders, static_lifetime, wrap_empty_binders, DynTy,
    Interner, QuantifiedWhereClauses, Substitution, TyBuilder, TyKind,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectSafetyError {
    LayoutError(LayoutError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectSafetyViolation {
    SizedSelf,
    SelfReferential,
    NonLifetimeBinder,
    Method(FunctionId, MethodViolationCode),
    AssocConst(ConstId),
    GAT(TypeAliasId),
    // This doesn't exist in rustc, but added for better visualization
    HasNonSafeSuperTrait(TraitId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MethodViolationCode {
    StaticMethod,
    ReferencesSelfInput,
    ReferencesSelfOutput,
    ReferencesImplTraitInTrait,
    AsyncFn,
    WhereClauseReferencesSelf,
    Generic,
    UndispatchableReceiver,
    HasNonLifetimeTypeParam,
    NonReceiverSelfParam,
}

// Basically, this is almost same as `rustc_trait_selection::traits::object_safety`
// but some difference;
//
// 1. While rustc gathers almost every violation, but this only early return on
//    first violation for perf.
//
// These can be changed anytime while implementing.
pub fn object_safety_of_trait_query(
    db: &dyn HirDatabase,
    trait_: TraitId,
) -> Result<Option<ObjectSafetyViolation>, ObjectSafetyError> {
    for super_trait in all_super_traits(db.upcast(), trait_).into_iter().skip(1) {
        if db.object_safety_of_trait(super_trait)?.is_some() {
            return Ok(Some(ObjectSafetyViolation::HasNonSafeSuperTrait(super_trait)));
        }
    }

    if generics_require_sized_self(db, trait_.into()) {
        return Ok(Some(ObjectSafetyViolation::SizedSelf));
    }

    // TODO: bound referencing self

    // TODO: non lifetime binder

    let trait_data = db.trait_data(trait_);
    for (_, assoc_item) in &trait_data.items {
        let item_violation = object_safety_violation_for_assoc_item(db, trait_, *assoc_item)?;
        if item_violation.is_some() {
            return Ok(item_violation);
        }
    }

    Ok(None)
}

fn generics_require_sized_self(db: &dyn HirDatabase, def: GenericDefId) -> bool {
    let krate = def.module(db.upcast()).krate();
    let Some(_sized) = db.lang_item(krate, LangItem::Sized).and_then(|l| l.as_trait()) else {
        return false;
    };

    let _predicates = db.generic_predicates(def);
    // TODO: elaborate with `utils::elaborate_clause_supertraits` and check `Self: Sized`

    false
}

fn object_safety_violation_for_assoc_item(
    db: &dyn HirDatabase,
    trait_: TraitId,
    item: AssocItemId,
) -> Result<Option<ObjectSafetyViolation>, ObjectSafetyError> {
    match item {
        AssocItemId::ConstId(it) => Ok(Some(ObjectSafetyViolation::AssocConst(it))),
        AssocItemId::FunctionId(it) => virtual_call_violations_for_method(db, trait_, it)
            .map(|v| v.map(|v| ObjectSafetyViolation::Method(it, v)))
            .map_err(ObjectSafetyError::LayoutError),
        AssocItemId::TypeAliasId(it) => {
            let generics = generics(db.upcast(), it.into());
            // rustc checks if the `generic_associate_type_extended` feature gate is set
            if generics.len_self() > 0 && db.type_alias_impl_traits(it).is_none() {
                Ok(Some(ObjectSafetyViolation::GAT(it)))
            } else {
                Ok(None)
            }
        }
    }
}

fn virtual_call_violations_for_method(
    db: &dyn HirDatabase,
    trait_: TraitId,
    func: FunctionId,
) -> Result<Option<MethodViolationCode>, LayoutError> {
    let func_data = db.function_data(func);
    if !func_data.has_self_param() {
        return Ok(Some(MethodViolationCode::StaticMethod));
    }

    // TODO: check self reference in params

    // TODO: check self reference in return type

    // TODO: check asyncness, RPIT

    let generic_params = db.generic_params(func.into());
    if generic_params.len_type_or_consts() > 0 {
        return Ok(Some(MethodViolationCode::Generic));
    }

    // Check if the receiver is a correct type like `Self`, `Box<Self>`, `Arc<Self>`, etc
    //
    // TODO: rustc does this in two steps :thinking_face:
    //       I'm doing only the second, real one, layout check
    // TODO: clean all the messes for building receiver types to check layout of

    // Check for types like `Rc<()>`
    let sig = callable_item_sig(db, func.into());
    // TODO: Getting receiver type that substituted `Self` by `()`. there might be more clever way?
    let subst = Substitution::from_iter(
        Interner,
        std::iter::repeat(TyBuilder::unit()).take(sig.len(Interner)),
    );
    let sig = sig.substitute(Interner, &subst);
    let receiver_ty = sig.params()[0].to_owned();
    let layout = db.layout_of_ty(receiver_ty, db.trait_environment(trait_.into()))?;

    if !matches!(layout.abi, rustc_abi::Abi::Scalar(..)) {
        return Ok(Some(MethodViolationCode::UndispatchableReceiver));
    }

    // Check for types like `Rc<dyn Trait>`
    // TODO: `dyn Trait` and receiver type building is a total mess
    let trait_ref =
        TyBuilder::trait_ref(db, trait_).fill_with_bound_vars(DebruijnIndex::INNERMOST, 0).build();
    let bound = wrap_empty_binders(WhereClause::Implemented(trait_ref));
    let bounds = QuantifiedWhereClauses::from_iter(Interner, [bound]);
    let dyn_trait = TyKind::Dyn(DynTy {
        bounds: make_single_type_binders(bounds),
        lifetime: static_lifetime(),
    })
    .intern(Interner);
    let sig = callable_item_sig(db, func.into());
    let subst = Substitution::from_iter(
        Interner,
        std::iter::once(dyn_trait)
            .chain(std::iter::repeat(TyBuilder::unit()))
            .take(sig.len(Interner)),
    );
    let sig = sig.substitute(Interner, &subst);
    let receiver_ty = sig.params()[0].to_owned();
    let layout = db.layout_of_ty(receiver_ty, db.trait_environment(trait_.into()))?;

    if !matches!(layout.abi, rustc_abi::Abi::ScalarPair(..)) {
        return Ok(Some(MethodViolationCode::UndispatchableReceiver));
    }

    Ok(None)
}
