module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.IExist

open Lean Elab Tactic Meta

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let before ← Tactic.saveState
  try
    let tactic ← `(tactic| iexists _)
    let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
    let some child ← generated.findM? fun goal => do
        return !(← goal.isAssignedOrDelayedAssigned)
      | before.restore; return RuleOutput.ofSpecs #[]
    let some _ ← Tactic.irisGoal? child
      | before.restore; return RuleOutput.ofSpecs #[]
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
