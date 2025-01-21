//! Trait solving using Chalk.

use core::fmt;
use std::env::var;

use chalk_ir::{fold::TypeFoldable, DebruijnIndex, GoalData};
use chalk_recursive::Cache;
use chalk_solve::{logging_db::LoggingRustIrDatabase, rust_ir, Solver};

use base_db::CrateId;
use hir_def::{
    lang_item::{LangItem, LangItemTarget},
    BlockId, TraitId,
};
use hir_expand::name::Name;
use intern::sym;
use rustc_next_trait_solver::solve::{HasChanged, SolverDelegateEvalExt};
use rustc_type_ir::{inherent::{SliceLike, Span as _}, solve::Certainty, InferCtxtLike, TypingMode};
use span::Edition;
use stdx::{never, panic_context};
use triomphe::Arc;

use crate::{
    db::HirDatabase, infer::unify::InferenceTable, next_solver::{infer::DbInternerInferExt, mapping::{convert_canonical_args_for_result, ChalkToNextSolver}, util::mini_canonicalize, DbInterner, DbIr, GenericArg, SolverContext}, utils::UnevaluatedConstEvaluatorFolder, AliasEq, AliasTy, Canonical, DomainGoal, Goal, Guidance, InEnvironment, Interner, ProjectionTy, ProjectionTyExt, Solution, TraitRefExt, Ty, TyKind, TypeFlags, WhereClause
};

/// This controls how much 'time' we give the Chalk solver before giving up.
const CHALK_SOLVER_FUEL: i32 = 1000;

#[derive(Debug, Copy, Clone)]
pub(crate) struct ChalkContext<'a> {
    pub(crate) db: &'a dyn HirDatabase,
    pub(crate) krate: CrateId,
    pub(crate) block: Option<BlockId>,
}

fn create_chalk_solver() -> chalk_recursive::RecursiveSolver<Interner> {
    let overflow_depth =
        var("CHALK_OVERFLOW_DEPTH").ok().and_then(|s| s.parse().ok()).unwrap_or(500);
    let max_size = var("CHALK_SOLVER_MAX_SIZE").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    chalk_recursive::RecursiveSolver::new(overflow_depth, max_size, Some(Cache::new()))
}

/// A set of clauses that we assume to be true. E.g. if we are inside this function:
/// ```rust
/// fn foo<T: Default>(t: T) {}
/// ```
/// we assume that `T: Default`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitEnvironment {
    pub krate: CrateId,
    pub block: Option<BlockId>,
    // FIXME make this a BTreeMap
    traits_from_clauses: Box<[(Ty, TraitId)]>,
    pub env: chalk_ir::Environment<Interner>,
}

impl TraitEnvironment {
    pub fn empty(krate: CrateId) -> Arc<Self> {
        Arc::new(TraitEnvironment {
            krate,
            block: None,
            traits_from_clauses: Box::default(),
            env: chalk_ir::Environment::new(Interner),
        })
    }

    pub fn new(
        krate: CrateId,
        block: Option<BlockId>,
        traits_from_clauses: Box<[(Ty, TraitId)]>,
        env: chalk_ir::Environment<Interner>,
    ) -> Arc<Self> {
        Arc::new(TraitEnvironment { krate, block, traits_from_clauses, env })
    }

    // pub fn with_block(self: &mut Arc<Self>, block: BlockId) {
    pub fn with_block(this: &mut Arc<Self>, block: BlockId) {
        Arc::make_mut(this).block = Some(block);
    }

    pub fn traits_in_scope_from_clauses(&self, ty: Ty) -> impl Iterator<Item = TraitId> + '_ {
        self.traits_from_clauses
            .iter()
            .filter_map(move |(self_ty, trait_id)| (*self_ty == ty).then_some(*trait_id))
    }
}

pub(crate) fn normalize_projection_query(
    db: &dyn HirDatabase,
    projection: ProjectionTy,
    env: Arc<TraitEnvironment>,
) -> Ty {
    if projection.substitution.iter(Interner).any(|arg| {
        arg.ty(Interner)
            .is_some_and(|ty| ty.data(Interner).flags.intersects(TypeFlags::HAS_TY_INFER))
    }) {
        never!(
            "Invoking `normalize_projection_query` with a projection type containing inference var"
        );
        return TyKind::Error.intern(Interner);
    }

    let mut table = InferenceTable::new(db, env);
    let ty = table.normalize_projection_ty(projection);
    table.resolve_completely(ty)
}

/// Solve a trait goal using Chalk.
pub(crate) fn trait_solve_query(
    db: &dyn HirDatabase,
    krate: CrateId,
    block: Option<BlockId>,
    goal: Canonical<InEnvironment<Goal>>,
) -> Option<Solution> {
    let detail = match &goal.value.goal.data(Interner) {
        GoalData::DomainGoal(DomainGoal::Holds(WhereClause::Implemented(it))) => {
            db.trait_data(it.hir_trait_id()).name.display(db.upcast(), Edition::LATEST).to_string()
        }
        GoalData::DomainGoal(DomainGoal::Holds(WhereClause::AliasEq(_))) => "alias_eq".to_owned(),
        _ => "??".to_owned(),
    };
    let _p = tracing::info_span!("trait_solve_query", ?detail).entered();
    tracing::info!("trait_solve_query({:?})", goal.value.goal);

    if let GoalData::DomainGoal(DomainGoal::Holds(WhereClause::AliasEq(AliasEq {
        alias: AliasTy::Projection(projection_ty),
        ..
    }))) = &goal.value.goal.data(Interner)
    {
        if let TyKind::BoundVar(_) = projection_ty.self_type_parameter(db).kind(Interner) {
            // Hack: don't ask Chalk to normalize with an unknown self type, it'll say that's impossible
            return Some(Solution::Ambig(Guidance::Unknown));
        }
    }

    // Chalk see `UnevaluatedConst` as a unique concrete value, but we see it as an alias for another const. So
    // we should get rid of it when talking to chalk.
    let goal = goal
        .try_fold_with(&mut UnevaluatedConstEvaluatorFolder { db }, DebruijnIndex::INNERMOST)
        .unwrap();

    // We currently don't deal with universes (I think / hope they're not yet
    // relevant for our use cases?)
    let u_canonical = chalk_ir::UCanonical { canonical: goal, universes: 1 };
    let check = false;
    match check {
        true => {
            dbg!(&u_canonical);
            let next_solver_res = solve_nextsolver(db, krate, block, &u_canonical);
            let chalk_res = solve(db, krate, block, &u_canonical);
            match (&chalk_res, &next_solver_res) {
                (Some(Solution::Unique(_)), Err(_)) => panic!("Next solver failed when Chalk did not.\n{:?}\n{:?}\n{:?}\n", u_canonical, chalk_res, next_solver_res),
                (None, Ok((_, Certainty::Yes, _))) => panic!("Next solver passed when Chalk did not.\n{:?}\n{:?}\n{:?}\n", u_canonical, chalk_res, next_solver_res),
                _ => {}
            }
            chalk_res
        }
        false => {
            solve(db, krate, block, &u_canonical)
        }
    }
}

fn solve(
    db: &dyn HirDatabase,
    krate: CrateId,
    block: Option<BlockId>,
    goal: &chalk_ir::UCanonical<chalk_ir::InEnvironment<chalk_ir::Goal<Interner>>>,
) -> Option<chalk_solve::Solution<Interner>> {
    let _p = tracing::info_span!("solve", ?krate, ?block).entered();
    let context = ChalkContext { db, krate, block };
    tracing::debug!("solve goal: {:?}", goal);
    let mut solver = create_chalk_solver();

    let fuel = std::cell::Cell::new(CHALK_SOLVER_FUEL);

    let should_continue = || {
        db.unwind_if_cancelled();
        let remaining = fuel.get();
        fuel.set(remaining - 1);
        if remaining == 0 {
            tracing::debug!("fuel exhausted");
        }
        remaining > 0
    };

    let mut solve = || {
        let _ctx = if is_chalk_debug() || is_chalk_print() {
            Some(panic_context::enter(format!("solving {goal:?}")))
        } else {
            None
        };
        let solution = if is_chalk_print() {
            let logging_db =
                LoggingRustIrDatabaseLoggingOnDrop(LoggingRustIrDatabase::new(context));
            solver.solve_limited(&logging_db.0, goal, &should_continue)
        } else {
            solver.solve_limited(&context, goal, &should_continue)
        };

        tracing::debug!("solve({:?}) => {:?}", goal, solution);

        solution
    };

    // don't set the TLS for Chalk unless Chalk debugging is active, to make
    // extra sure we only use it for debugging
    if is_chalk_debug() {
        crate::tls::set_current_program(db, solve)
    } else {
        solve()
    }
}

fn solve_nextsolver(
    db: &dyn HirDatabase,
    krate: CrateId,
    block: Option<BlockId>,
    goal: &chalk_ir::UCanonical<chalk_ir::InEnvironment<chalk_ir::Goal<Interner>>>,
) -> Result<(HasChanged, Certainty, rustc_type_ir::Canonical<DbInterner, Vec<GenericArg>>), rustc_type_ir::solve::NoSolution> {
    crate::next_solver::tls::with_db(db, || {
        // FIXME: should use analysis_in_body, but that needs GenericDefId::Block
        let context = SolverContext(DbIr::new(db, krate, block).infer_ctxt().build(TypingMode::non_body_analysis()));

        match goal.canonical.value.goal.data(Interner) {
            // FIXME: args here should be...what? not empty
            GoalData::All(goals) if goals.is_empty(Interner) => return Ok((HasChanged::No, Certainty::Yes, mini_canonicalize(vec![]))),
            _ => {}
        }

        let goal = goal.canonical.to_nextsolver(context.cx());
        dbg!(&goal);

        let (goal, var_values) = context.instantiate_canonical(crate::next_solver::Span::dummy(), &goal);
        dbg!(&var_values);

        let (res, _) =
            context.evaluate_root_goal(goal, rustc_next_trait_solver::solve::GenerateProofTree::No);

        let canonical_var_values: rustc_type_ir::Canonical<DbInterner, Vec<_>> = mini_canonicalize(var_values.var_values.iter().map(|g| context.0.resolve_vars_if_possible(g)).collect());

        res.map(|r| (r.0, r.1, canonical_var_values))
    })
}

#[derive(Clone, Debug)]
pub enum NextTraitSolveResult {
    Certain(chalk_ir::Canonical<chalk_ir::ConstrainedSubst<Interner>>),
    Uncertain(chalk_ir::Canonical<chalk_ir::ConstrainedSubst<Interner>>),
    NoSolution,
}

impl NextTraitSolveResult {
    pub fn no_solution(self) -> bool {
        matches!(self, NextTraitSolveResult::NoSolution)
    }

    pub fn certain(self) -> bool {
        matches!(self, NextTraitSolveResult::Certain(..))
    }
}

/// Solve a trait goal using Chalk.
pub fn next_trait_solve(
    db: &dyn HirDatabase,
    krate: CrateId,
    block: Option<BlockId>,
    goal: Canonical<InEnvironment<Goal>>,
) -> NextTraitSolveResult {
    let detail = match &goal.value.goal.data(Interner) {
        GoalData::DomainGoal(DomainGoal::Holds(WhereClause::Implemented(it))) => {
            db.trait_data(it.hir_trait_id()).name.display(db.upcast(), Edition::LATEST).to_string()
        }
        GoalData::DomainGoal(DomainGoal::Holds(WhereClause::AliasEq(_))) => "alias_eq".to_owned(),
        _ => "??".to_owned(),
    };
    let _p = tracing::info_span!("trait_solve_query", ?detail).entered();
    tracing::info!("trait_solve_query({:?})", goal.value.goal);

    if let GoalData::DomainGoal(DomainGoal::Holds(WhereClause::AliasEq(AliasEq {
        alias: AliasTy::Projection(projection_ty),
        ..
    }))) = &goal.value.goal.data(Interner)
    {
        if let TyKind::BoundVar(_) = projection_ty.self_type_parameter(db).kind(Interner) {
            // Hack: don't ask Chalk to normalize with an unknown self type, it'll say that's impossible
            // FIXME
            return NextTraitSolveResult::Uncertain(convert_canonical_args_for_result(db, mini_canonicalize(vec![])));
        }
    }

    // Chalk see `UnevaluatedConst` as a unique concrete value, but we see it as an alias for another const. So
    // we should get rid of it when talking to chalk.
    let goal = goal
        .try_fold_with(&mut UnevaluatedConstEvaluatorFolder { db }, DebruijnIndex::INNERMOST)
        .unwrap();

    // We currently don't deal with universes (I think / hope they're not yet
    // relevant for our use cases?)
    let u_canonical = chalk_ir::UCanonical { canonical: goal, universes: 1 };
    dbg!(&u_canonical);

    let next_solver_res = solve_nextsolver(db, krate, block, &u_canonical);
    let chalk_res = solve(db, krate, block, &u_canonical);
    match (&chalk_res, &next_solver_res) {
        (Some(Solution::Unique(_)), Err(_)) => eprintln!("Next solver failed when Chalk did not.\n{:?}\n{:?}\n{:?}\n", u_canonical, chalk_res, next_solver_res),
        (Some(Solution::Unique(_)), Ok((_, Certainty::Maybe(_), _))) => eprintln!("Next solver failed when Chalk did not.\n{:?}\n{:?}\n{:?}\n", u_canonical, chalk_res, next_solver_res),
        (None, Ok((_, Certainty::Yes, _))) => eprintln!("Next solver passed when Chalk did not.\n{:?}\n{:?}\n{:?}\n", u_canonical, chalk_res, next_solver_res),
        _ => {}
    }

    match next_solver_res {
        Err(_) => NextTraitSolveResult::NoSolution,
        Ok((_, Certainty::Yes, args)) => NextTraitSolveResult::Certain(convert_canonical_args_for_result(db, args)),
        Ok((_, Certainty::Maybe(_), args)) => NextTraitSolveResult::Uncertain(convert_canonical_args_for_result(db, args)),
    }
}

struct LoggingRustIrDatabaseLoggingOnDrop<'a>(LoggingRustIrDatabase<Interner, ChalkContext<'a>>);

impl Drop for LoggingRustIrDatabaseLoggingOnDrop<'_> {
    fn drop(&mut self) {
        tracing::info!("chalk program:\n{}", self.0);
    }
}

fn is_chalk_debug() -> bool {
    std::env::var("CHALK_DEBUG").is_ok()
}

fn is_chalk_print() -> bool {
    std::env::var("CHALK_PRINT").is_ok()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FnTrait {
    // Warning: Order is important. If something implements `x` it should also implement
    // `y` if `y <= x`.
    FnOnce,
    FnMut,
    Fn,
}

impl fmt::Display for FnTrait {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FnTrait::FnOnce => write!(f, "FnOnce"),
            FnTrait::FnMut => write!(f, "FnMut"),
            FnTrait::Fn => write!(f, "Fn"),
        }
    }
}

impl FnTrait {
    pub const fn function_name(&self) -> &'static str {
        match self {
            FnTrait::FnOnce => "call_once",
            FnTrait::FnMut => "call_mut",
            FnTrait::Fn => "call",
        }
    }

    const fn lang_item(self) -> LangItem {
        match self {
            FnTrait::FnOnce => LangItem::FnOnce,
            FnTrait::FnMut => LangItem::FnMut,
            FnTrait::Fn => LangItem::Fn,
        }
    }

    pub const fn from_lang_item(lang_item: LangItem) -> Option<Self> {
        match lang_item {
            LangItem::FnOnce => Some(FnTrait::FnOnce),
            LangItem::FnMut => Some(FnTrait::FnMut),
            LangItem::Fn => Some(FnTrait::Fn),
            _ => None,
        }
    }

    pub const fn to_chalk_ir(self) -> rust_ir::ClosureKind {
        match self {
            FnTrait::FnOnce => rust_ir::ClosureKind::FnOnce,
            FnTrait::FnMut => rust_ir::ClosureKind::FnMut,
            FnTrait::Fn => rust_ir::ClosureKind::Fn,
        }
    }

    pub fn method_name(self) -> Name {
        match self {
            FnTrait::FnOnce => Name::new_symbol_root(sym::call_once.clone()),
            FnTrait::FnMut => Name::new_symbol_root(sym::call_mut.clone()),
            FnTrait::Fn => Name::new_symbol_root(sym::call.clone()),
        }
    }

    pub fn get_id(self, db: &dyn HirDatabase, krate: CrateId) -> Option<TraitId> {
        let target = db.lang_item(krate, self.lang_item())?;
        match target {
            LangItemTarget::Trait(t) => Some(t),
            _ => None,
        }
    }
}
