-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.IExist

open Lean Elab Tactic Meta

private def openGoals (goals : List MVarId) : MetaM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

/--
  Solve only auxiliary term metavariables that no other open goal depends on.
  Witnesses occurring in the Iris child remain unassigned for later unification.
-/
private def solveIndependentAuxGoals (goals : Array MVarId) : TacticM Unit := do
  for goal in goals do
    if ← goal.isAssignedOrDelayedAssigned then continue
    if (← Tactic.irisGoal? goal).isSome then continue
    let isPure ← goal.withContext do
      isProp (← instantiateMVars (← goal.getType))
    if isPure then continue
    let referenced ← goals.anyM λ other => do
      if other == goal || (← other.isAssignedOrDelayedAssigned) then return false
      return (← other.withContext other.getMVarDependencies).contains goal
    if referenced then continue
    let before ← Tactic.saveState
    try
      let tactic ← `(tactic| assumption)
      let generated ← withSuppressedMessages <| evalTacticAt tactic goal
      let remaining ← openGoals generated
      unless (← goal.isAssignedOrDelayedAssigned) && remaining.isEmpty do
        before.restore
    catch _ => before.restore

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let before ← Tactic.saveState
  try
    let tactic ← `(tactic| iexists _)
    let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
    let generated ← openGoals generated
    let some child ← generated.findM? fun goal => do
        return (← Tactic.irisGoal? goal).isSome
      | before.restore; return RuleOutput.ofSpecs #[]
    solveIndependentAuxGoals generated
    let child ← SubGoal.ofMVar child
    return .ofSpec {
      goals := #[child]
      postState := ← Meta.saveState
      effect := {}
    }
  catch exception =>
    trace[ibubble.rule] "iexists failed: {exception.toMessageData}"
    before.restore
    return RuleOutput.ofSpecs #[]

end Bubble.Rule.Tactic.IExist
