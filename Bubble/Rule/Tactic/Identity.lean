module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.Identity

open Lean Meta Qq
open Iris.ProofMode

def run (input : RuleInput) : Lean.Elab.Tactic.TacticM RuleOutput := do
  input.state.restore
  input.goal.withContext do
    let some irisGoal ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
    let { prop, goal := target, .. } := irisGoal
    /- When both views exist, `FromAnd` gives `isplit` a shared-context
    decomposition and dominates this linear `FromSep` decomposition. -/
    let beforeAndProbe ← Meta.saveState
    let andLeft ← mkFreshExprMVarQ prop
    let andRight ← mkFreshExprMVarQ prop
    match ← Tactic.trySynthInstanceProbeQ q(FromAnd $target $andLeft $andRight) with
    | .some _ =>
        beforeAndProbe.restore
        return RuleOutput.ofSpecs #[]
    | .none | .undef => beforeAndProbe.restore
    let left ← mkFreshExprMVarQ prop
    let right ← mkFreshExprMVarQ prop
    let .some _ ← Tactic.trySynthInstanceProbeQ q(FromSep $target $left $right)
      | return RuleOutput.ofSpecs #[]
    let left : Q($prop) ← instantiateMVars left
    let right : Q($prop) ← instantiateMVars right
    let tag ← input.goal.getTag
    let mut goals : Array SubGoal := #[]
    for childTarget in #[left, right] do
      let template := { irisGoal with goal := childTarget }
      let child ← mkFreshExprSyntheticOpaqueMVar template.toExpr tag
      goals := goals.push (← SubGoal.ofMVar child.mvarId!)
    return .ofSpec {
      goals
      postState := ← Meta.saveState
      effect := { multiGoalAction? := some .partitionContext }
    }

end Bubble.Rule.Tactic.Identity
