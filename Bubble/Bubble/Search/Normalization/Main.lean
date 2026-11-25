-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.TreeM
public meta import Bubble.Search.Configure
public meta import Bubble.Search.Normalization.Intro
public meta import Bubble.Search.Normalization.Cases
public meta import Bubble.Search.Normalization.Rewrite
public meta import Bubble.Search.Normalization.Simp

public meta section

namespace Bubble.Search

open Lean Lean.Meta Elab Tactic
open Normalization

private def normalizationSteps : Array Step :=
  #[introStep, casesStep, rewriteStep, simpStep]

private def runFirstNormStep (input : StepInput) : TacticM StepResult := do
  for step in normalizationSteps do
    -- trace[ibubble.search.norm] "trying {step.label} at {input.goal.name}"
    if let some result ← tryAttempt <| step.run input then
      trace[ibubble.search.norm] "applied {step.label} at {input.goal.name}"
      return result
  trace[ibubble.search.norm] "no normalization step applies at {input.goal.name}"
  return .unchanged

/-- Repeatedly normalize a metavariable goal until it is proved or reaches a fixed point. -/
partial def normalizeGoalMVar (goal : MVarId) (depth : Nat) (maxIterations : Nat)
    (enableSimp : Bool) (goalMVars : Std.HashSet MVarId)
    (observer? : Option NormStepObserver := none) :
    TacticM (NormSeqResult × Array MVarId) := do
  go 0 goal #[]
where
  observeStep (preState? : Option Meta.SavedState) (preGoal : MVarId)
      (postGoals : Array MVarId) (tactic? : Option (TSyntax `tactic)) :
      TacticM Unit := do
    let some observer := observer? | return
    let some preState := preState? | return
    let some tactic := tactic? | return
    let postState ← liftM (m := MetaM) saveState
    observer preState preGoal tactic postState postGoals

  go (iteration : Nat) (goal : MVarId) (remaining : Array MVarId) :
      TacticM (NormSeqResult × Array MVarId) := do
    if iteration >= maxIterations then
      throwError "ibubble: exceeded {maxIterations} normalization iterations"
    let input : StepInput := { goal, depth, enableSimp, goalMVars }
    let preState? ← match observer? with
      | some _ => liftM (m := MetaM) (some <$> saveState)
      | none => pure none
    match ← runFirstNormStep input with
    | .proved stepRemaining tactic? =>
        observeStep preState? goal stepRemaining tactic?
        return (.proved, remaining ++ stepRemaining)
    | .changed newGoal stepRemaining tactic? =>
        let postGoals := #[newGoal] ++ stepRemaining
        observeStep preState? goal postGoals tactic?
        go (iteration + 1) newGoal (remaining ++ stepRemaining)
    | .unchanged =>
        let result : NormSeqResult :=
          if iteration == 0 then .unchanged else .changed goal
        return (result, remaining)

/-- Normalize one search goal and explicitly return any auxiliary Lean goals. -/
def normalizeGoal (config : SearchConfig) (goalRef : GoalRef) : TreeM (Array MVarId) := do
  let goal ← goalRef.get
  match goal.normalizationState with
  | .provenByNorm .. | .normal .. => return #[]
  | .notNormal =>
    goal.preNormState.restore

    /- Compare the spatial hypotheses before and after normalization. -/
    let preHyps ← spatialHypsOf goal.preNormGoal
    let (result, remaining) ← normalizeGoalMVar goal.preNormGoal goal.depth
      config.maxNormIterations config.enableSimp? goal.unassignedMvars
    let postHyps ← match result with
      | .proved => pure #[]
      | .unchanged => pure preHyps
      | .changed postGoal => spatialHypsOf postGoal
    let postState ← liftM (m := MetaM) saveState
    let generated := postHyps.filter fun hyp => !preHyps.contains hyp
    let consumed := preHyps.filter fun hyp => !postHyps.contains hyp

    match result with
    | .proved => goalRef.modify λ goal => goal.setNormalizationState <|
      .provenByNorm postState generated consumed
    | .changed postGoal =>
      let mvars ← postGoal.withContext postGoal.getMVarDependencies
      goalRef.modify λ goal => goal.setNormalizationState
        (.normal postGoal postState generated consumed)
        |>.setUnassignedMvars mvars
    | .unchanged => goalRef.modify λ goal => goal.setNormalizationState <|
      (.normal goal.preNormGoal postState #[] #[])
    return remaining

end Bubble.Search
