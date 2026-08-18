module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.ILeftRight

open Lean Elab Tactic Meta

inductive Side where
  | left
  | right

private def runSide (side : Side) (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let before ← Tactic.saveState
  try
    let tactic ← match side with
      | .left => `(tactic| ileft)
      | .right => `(tactic| iright)
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
    trace[ibubble.rule] "ileft/iright failed: {exception.toMessageData}"
    before.restore
    return RuleOutput.ofSpecs #[]

def runLeft : RuleRunner := runSide .left
def runRight : RuleRunner := runSide .right

end Bubble.Rule.Tactic.ILeftRight
