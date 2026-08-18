module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Backward

open Lean Elab Tactic Meta

initialize registerTraceClass `ibubble.backward

private def openGoals (goals : List MVarId) : MetaM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let before ← Tactic.saveState
  let decl := mkIdent input.matchResult.rule.id.name
  let tactic ← `(tactic| iapply $decl:ident)
  try
    let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
    unless ← input.goal.isAssignedOrDelayedAssigned do
      before.restore
      return RuleOutput.ofSpecs #[]
    let mut childGoals : Array MVarId := #[]
    for goal in generated do
      unless ← goal.isAssignedOrDelayedAssigned do
        match ← Tactic.irisGoal? goal with
        | some _ =>
            childGoals := childGoals.push goal
        | none =>
            let isPure ← goal.withContext do
              isProp (← instantiateMVars (← goal.getType))
            if !isPure || input.config.pureStop? then
              continue
            else
              let produced ← withSuppressedMessages <|
                evalTacticAt input.config.pureSolver goal
              let remaining ← openGoals produced
              unless remaining.isEmpty do
                before.restore
                return RuleOutput.ofSpecs #[]
    let goals ← childGoals.mapM fun goal =>
      liftM (m := MetaM) <| SubGoal.ofMVar goal
    return .ofSpec {
      goals
      postState := ← Meta.saveState
      effect := {
        multiGoalAction? := if goals.size > 1 then some .partitionContext else none
      }
    }
  catch exception =>
    trace[ibubble.rule] "backward {input.matchResult.rule.id.name} failed: {exception.toMessageData}"
    before.restore
    return RuleOutput.ofSpecs #[]

end Bubble.Rule.Backward
