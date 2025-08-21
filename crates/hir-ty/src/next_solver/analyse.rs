//! An infrastructure to mechanically analyse proof trees.
//! Mostly copied from
//! https://github.com/rust-lang/rust/blob/040a98af70f0a7da03f3d5356531b28a2a7a77e4/compiler/rustc_trait_selection/src/solve/inspect/analyse.rs

use std::cell::RefCell;

use rustc_next_trait_solver::{
    delegate::SolverDelegate,
    resolve::eager_resolve_vars,
    solve::{SolverDelegateEvalExt, inspect::instantiate_canonical_state},
};
use rustc_type_ir::{
    InferCtxtLike, VisitorResult,
    error::TypeError,
    inherent::{IntoKind, Span as _},
    solve::{
        Certainty, GoalSource, MaybeCause, NoSolution, QueryResult,
        inspect::{
            CanonicalState, GoalEvaluation, GoalEvaluationKind, Probe, ProbeKind, ProbeStep,
        },
    },
};
use stdx::never;

use crate::next_solver::{fulfill::NextSolverError, infer::at::ToTrace};

use super::{
    DbInterner, GenericArg, Goal, NormalizesTo, ParamEnv, Predicate, PredicateKind, SolverContext,
    Span, Term,
    fulfill::FulfillmentCtxt,
    infer::{
        DefineOpaqueTypes, InferCtxt, InferOk, InferResult,
        traits::{Obligation, ObligationCause, PredicateObligation},
    },
};

pub struct InspectConfig {
    pub max_depth: usize,
}

pub struct InspectGoal<'a, 'db> {
    infcx: &'a SolverContext<'db>,
    depth: usize,
    orig_values: Vec<GenericArg<'db>>,
    goal: Goal<'db, Predicate<'db>>,
    result: Result<Certainty, NoSolution>,
    evaluation_kind: GoalEvaluationKind<DbInterner<'db>>,
    normalizes_to_term_hack: Option<NormalizesToTermHack<'db>>,
    source: GoalSource,
}

impl<'a, 'db> InspectGoal<'a, 'db> {
    pub fn goal(&self) -> Goal<'db, Predicate<'db>> {
        self.goal
    }

    pub fn result(&self) -> Result<Certainty, NoSolution> {
        self.result
    }

    fn candidates_recur(
        &'a self,
        candidates: &mut Vec<InspectCandidate<'a, 'db>>,
        steps: &mut Vec<&'a ProbeStep<DbInterner<'db>>>,
        probe: &'a Probe<DbInterner<'db>>,
    ) {
        let mut shallow_certainty = None;
        for step in &probe.steps {
            match *step {
                ProbeStep::AddGoal(..) | ProbeStep::RecordImplArgs { .. } => steps.push(step),
                ProbeStep::MakeCanonicalResponse { shallow_certainty: c } => {
                    assert!(matches!(
                        shallow_certainty.replace(c),
                        None | Some(Certainty::Maybe(MaybeCause::Ambiguity))
                    ));
                }
                ProbeStep::NestedProbe(ref probe) => {
                    match probe.kind {
                        // These never assemble candidates for the goal we're trying to solve.
                        ProbeKind::ProjectionCompatibility | ProbeKind::ShadowedEnvProbing => {
                            continue;
                        }

                        ProbeKind::NormalizedSelfTyAssembly
                        | ProbeKind::UnsizeAssembly
                        | ProbeKind::Root { .. }
                        | ProbeKind::TraitCandidate { .. }
                        | ProbeKind::OpaqueTypeStorageLookup { .. }
                        | ProbeKind::RigidAlias { .. } => {
                            // Nested probes have to prove goals added in their parent
                            // but do not leak them, so we truncate the added goals
                            // afterwards.
                            let num_steps = steps.len();
                            self.candidates_recur(candidates, steps, probe);
                            steps.truncate(num_steps);
                        }
                    }
                }
            }
        }

        match probe.kind {
            ProbeKind::ProjectionCompatibility | ProbeKind::ShadowedEnvProbing => {
                never!()
            }

            ProbeKind::NormalizedSelfTyAssembly | ProbeKind::UnsizeAssembly => {}

            // We add a candidate even for the root evaluation if there
            // is only one way to prove a given goal, e.g. for `WellFormed`.
            ProbeKind::Root { result }
            | ProbeKind::TraitCandidate { source: _, result }
            | ProbeKind::OpaqueTypeStorageLookup { result }
            | ProbeKind::RigidAlias { result } => {
                // We only add a candidate if `shallow_certainty` was set, which means
                // that we ended up calling `evaluate_added_goals_and_make_canonical_response`.
                if let Some(shallow_certainty) = shallow_certainty {
                    candidates.push(InspectCandidate {
                        goal: self,
                        kind: probe.kind,
                        steps: steps.clone(),
                        final_state: probe.final_state,
                        shallow_certainty,
                        result,
                    });
                }
            }
        }
    }

    pub fn candidates(&'a self) -> Vec<InspectCandidate<'a, 'db>> {
        let mut candidates = vec![];
        let last_eval_step = match &self.evaluation_kind {
            // An annoying edge case in case the recursion limit is 0.
            GoalEvaluationKind::Overflow => return candidates,
            GoalEvaluationKind::Evaluation { final_revision } => final_revision,
        };

        let mut nested_goals = vec![];
        self.candidates_recur(&mut candidates, &mut nested_goals, last_eval_step);

        candidates
    }

    pub fn unique_applicable_candidate(&'a self) -> Option<InspectCandidate<'a, 'db>> {
        // FIXME(rustc): This does not handle impl candidates
        // hidden by env candidates.
        let mut candidates = self.candidates();
        candidates.retain(|c| c.result().is_ok());
        candidates.pop().filter(|_| candidates.is_empty())
    }

    fn new(
        infcx: &'a InferCtxt<'db>,
        depth: usize,
        root: GoalEvaluation<DbInterner<'db>>,
        term_hack_and_nested_certainty: Option<(
            NormalizesToTermHack<'db>,
            Result<Certainty, NoSolution>,
        )>,
        source: GoalSource,
    ) -> Self {
        let infcx = <&SolverContext<'db>>::from(infcx);

        let GoalEvaluation { uncanonicalized_goal, orig_values, kind, result } = root;

        // If there's a normalizes-to goal, AND the evaluation result with the result of
        // constraining the normalizes-to RHS and computing the nested goals.
        let result = result.and_then(|ok| {
            let nested_goals_certainty =
                term_hack_and_nested_certainty.map_or(Ok(Certainty::Yes), |(_, c)| c)?;
            Ok(ok.value.certainty.and(nested_goals_certainty))
        });

        InspectGoal {
            infcx,
            depth,
            orig_values,
            goal: eager_resolve_vars(infcx, uncanonicalized_goal),
            result,
            evaluation_kind: kind,
            normalizes_to_term_hack: term_hack_and_nested_certainty.map(|(n, _)| n),
            source,
        }
    }

    pub fn visit_with<V: ProofTreeVisitor<'db>>(&self, visitor: &mut V) -> V::Result {
        if self.depth < visitor.config().max_depth {
            match visitor.visit_goal(self).branch() {
                std::ops::ControlFlow::Continue(()) => {}
                std::ops::ControlFlow::Break(r) => return V::Result::from_residual(r),
            }
        }

        V::Result::output()
    }
}

/// The expected term of a `NormalizesTo` goal gets replaced
/// with an unconstrained inference variable when computing
/// `NormalizesTo` goals and we return the nested goals to the
/// caller, who also equates the actual term with the expected.
///
/// This is an implementation detail of the trait solver and
/// not something we want to leak to users. We therefore
/// treat `NormalizesTo` goals as if they apply the expected
/// type at the end of each candidate.
#[derive(Clone, Copy)]
struct NormalizesToTermHack<'db> {
    term: Term<'db>,
    unconstrained_term: Term<'db>,
}

struct ObligationCtxt<'a, 'db> {
    infcx: &'a InferCtxt<'db>,
    fulfillment_ctxt: RefCell<FulfillmentCtxt<'db>>,
}

impl<'a, 'db> ObligationCtxt<'a, 'db> {
    pub fn new(infcx: &'a InferCtxt<'db>) -> Self {
        let fulfillment_ctxt = RefCell::new(FulfillmentCtxt::new(infcx));
        Self { infcx, fulfillment_ctxt }
    }

    pub fn register_obligation(&self, obligation: PredicateObligation<'db>) {
        self.fulfillment_ctxt.borrow_mut().register_predicate_obligation(self.infcx, obligation);
    }

    pub fn register_obligations(
        &self,
        obligations: impl IntoIterator<Item = PredicateObligation<'db>>,
    ) {
        for obligation in obligations {
            self.fulfillment_ctxt.borrow_mut().register_predicate_obligation(self.infcx, obligation)
        }
    }

    pub fn register_infer_ok_obligations<T>(&self, infer_ok: InferOk<'db, T>) -> T {
        let InferOk { value, obligations } = infer_ok;
        for obligation in obligations {
            self.fulfillment_ctxt
                .borrow_mut()
                .register_predicate_obligation(self.infcx, obligation);
        }
        value
    }

    pub fn eq<T: ToTrace<'db>>(
        &self,
        cause: &ObligationCause,
        param_env: ParamEnv<'db>,
        expected: T,
        actual: T,
    ) -> Result<(), TypeError<DbInterner<'db>>> {
        self.infcx
            .at(cause, param_env)
            .eq(DefineOpaqueTypes::Yes, expected, actual)
            .map(|infer_ok| self.register_infer_ok_obligations(infer_ok))
    }

    pub fn select_all_or_error(&self) -> Vec<NextSolverError<'db>> {
        self.fulfillment_ctxt.borrow_mut().select_all_or_error(self.infcx)
    }
}

impl<'db> NormalizesToTermHack<'db> {
    /// Relate the `term` with the new `unconstrained_term` created
    /// when computing the proof tree for this `NormalizesTo` goals.
    /// This handles nested obligations.
    fn constrain_and(
        &self,
        infcx: &InferCtxt<'db>,
        param_env: ParamEnv<'db>,
        f: impl FnOnce(&ObligationCtxt<'_, 'db>),
    ) -> Result<Certainty, NoSolution> {
        let ocx = ObligationCtxt::new(infcx);
        ocx.eq(&ObligationCause::dummy(), param_env, self.term, self.unconstrained_term)?;
        f(&ocx);
        let errors = ocx.select_all_or_error();
        if errors.is_empty() {
            Ok(Certainty::Yes)
        } else if errors.iter().all(|e| !e.is_true_error()) {
            Ok(Certainty::AMBIGUOUS)
        } else {
            Err(NoSolution)
        }
    }
}

pub struct InspectCandidate<'a, 'db> {
    goal: &'a InspectGoal<'a, 'db>,
    kind: ProbeKind<DbInterner<'db>>,
    steps: Vec<&'a ProbeStep<DbInterner<'db>>>,
    final_state: CanonicalState<DbInterner<'db>, ()>,
    result: QueryResult<DbInterner<'db>>,
    shallow_certainty: Certainty,
}

impl<'a, 'db> InspectCandidate<'a, 'db> {
    pub fn kind(&self) -> ProbeKind<DbInterner<'db>> {
        self.kind
    }

    pub fn result(&self) -> Result<Certainty, NoSolution> {
        self.result.map(|c| c.value.certainty)
    }

    pub fn goal(&self) -> &'a InspectGoal<'a, 'db> {
        self.goal
    }

    /// Certainty passed into `evaluate_added_goals_and_make_canonical_response`.
    ///
    /// If this certainty is `Yes`, then we must be confident that the candidate
    /// must hold iff it's nested goals hold. This is not true if the certainty is
    /// `Maybe(..)`, which suggests we forced ambiguity instead.
    ///
    /// This is *not* the certainty of the candidate's full nested evaluation, which
    /// can be accessed with [`Self::result`] instead.
    pub fn shallow_certainty(&self) -> Certainty {
        self.shallow_certainty
    }

    /// Visit all nested goals of this candidate without rolling
    /// back their inference constraints. This function modifies
    /// the state of the `infcx`.
    pub fn visit_nested_no_probe<V: ProofTreeVisitor<'db>>(&self, visitor: &mut V) -> V::Result {
        for goal in self.instantiate_nested_goals() {
            goal.visit_with(visitor);
        }

        V::Result::output()
    }

    /// Instantiate the nested goals for the candidate without rolling back their
    /// inference constraints. This function modifies the state of the `infcx`.
    pub fn instantiate_nested_goals(&self) -> Vec<InspectGoal<'a, 'db>> {
        let infcx = self.goal.infcx;
        let param_env = self.goal.goal.param_env;
        let mut orig_values = self.goal.orig_values.to_vec();

        let mut instantiated_goals = vec![];
        for step in &self.steps {
            match **step {
                ProbeStep::AddGoal(source, goal) => instantiated_goals.push((
                    source,
                    instantiate_canonical_state(
                        infcx,
                        Span::dummy(),
                        param_env,
                        &mut orig_values,
                        goal,
                    ),
                )),
                ProbeStep::RecordImplArgs { .. } => {}
                ProbeStep::MakeCanonicalResponse { .. } | ProbeStep::NestedProbe(_) => {
                    unreachable!()
                }
            }
        }

        let () = instantiate_canonical_state(
            infcx,
            Span::dummy(),
            param_env,
            &mut orig_values,
            self.final_state,
        );

        if let Some(term_hack) = &self.goal.normalizes_to_term_hack {
            // FIXME(rustc): We ignore the expected term of `NormalizesTo` goals
            // when computing the result of its candidates. This is
            // scuffed.
            let _ = term_hack.constrain_and(infcx, param_env, |_| {});
        }

        instantiated_goals
            .into_iter()
            .map(|(source, goal)| {
                self.instantiate_proof_tree_for_nested_goal(source, goal, Span::dummy())
            })
            .collect()
    }

    pub fn instantiate_proof_tree_for_nested_goal(
        &self,
        source: GoalSource,
        goal: Goal<'db, Predicate<'db>>,
        span: Span,
    ) -> InspectGoal<'a, 'db> {
        let infcx = self.goal.infcx;
        match goal.predicate.kind().no_bound_vars() {
            Some(PredicateKind::NormalizesTo(NormalizesTo { alias, term })) => {
                let unconstrained_term = infcx.next_term_var_of_kind(term);
                let goal =
                    goal.with(infcx.0.cx(), NormalizesTo { alias, term: unconstrained_term });
                // We have to use a `probe` here as evaluating a `NormalizesTo` can constrain the
                // expected term. This means that candidates which only fail due to nested goals
                // and which normalize to a different term then the final result could ICE: when
                // building their proof tree, the expected term was unconstrained, but when
                // instantiating the candidate it is already constrained to the result of another
                // candidate.
                let normalizes_to_term_hack = NormalizesToTermHack { term, unconstrained_term };
                let (proof_tree, nested_goals_result) = infcx.probe(|_| {
                    // Here, if we have any nested goals, then we make sure to apply them
                    // considering the constrained RHS, and pass the resulting certainty to
                    // `InspectGoal::new` so that the goal has the right result (and maintains
                    // the impression that we don't do this normalizes-to infer hack at all).
                    let (nested, proof_tree) = infcx.evaluate_root_goal_for_proof_tree(goal, span);
                    let nested_goals_result = nested.and_then(|(nested, _)| {
                        normalizes_to_term_hack.constrain_and(
                            infcx,
                            proof_tree.uncanonicalized_goal.param_env,
                            |ocx| {
                                ocx.register_obligations(nested.0.into_iter().map(|(_, goal)| {
                                    Obligation::new(
                                        infcx.cx(),
                                        ObligationCause::dummy(),
                                        goal.param_env,
                                        goal.predicate,
                                    )
                                }));
                            },
                        )
                    });
                    (proof_tree, nested_goals_result)
                });
                InspectGoal::new(
                    infcx,
                    self.goal.depth + 1,
                    proof_tree,
                    Some((normalizes_to_term_hack, nested_goals_result)),
                    source,
                )
            }
            _ => {
                // We're using a probe here as evaluating a goal could constrain
                // inference variables by choosing one candidate. If we then recurse
                // into another candidate who ends up with different inference
                // constraints, we get an ICE if we already applied the constraints
                // from the chosen candidate.
                let proof_tree =
                    infcx.probe(|_| infcx.evaluate_root_goal_for_proof_tree(goal, span).1);
                InspectGoal::new(infcx, self.goal.depth + 1, proof_tree, None, source)
            }
        }
    }
}

pub trait ProofTreeVisitor<'db> {
    type Result: VisitorResult;

    fn config(&self) -> InspectConfig {
        InspectConfig { max_depth: 10 }
    }

    fn visit_goal(&mut self, goal: &InspectGoal<'_, 'db>) -> Self::Result;
}

impl<'db> InferCtxt<'db> {
    fn visit_proof_tree<V: ProofTreeVisitor<'db>>(
        &self,
        goal: Goal<'db, Predicate<'db>>,
        visitor: &mut V,
    ) -> V::Result {
        self.visit_proof_tree_at_depth(goal, 0, visitor)
    }

    fn visit_proof_tree_at_depth<V: ProofTreeVisitor<'db>>(
        &self,
        goal: Goal<'db, Predicate<'db>>,
        depth: usize,
        visitor: &mut V,
    ) -> V::Result {
        let (_, proof_tree) = <&SolverContext<'db>>::from(self)
            .evaluate_root_goal_for_proof_tree(goal, Span::dummy());
        visitor.visit_goal(&InspectGoal::new(self, depth, proof_tree, None, GoalSource::Misc))
    }
}
