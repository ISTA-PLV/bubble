-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Tactic.IPureIntro

open Lean Elab Lean.Elab.Tactic Meta

private def openGoals (goals : List MVarId) : MetaM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let before ← Lean.Elab.Tactic.saveState
  try
    let tactic ← `(tactic| ipureintro)
    let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
    unless ← input.goal.isAssignedOrDelayedAssigned do
      before.restore
      return RuleOutput.ofSpecs #[]
    let pending ← if input.config.pureStop? then
      openGoals generated
    else do
      let mut remaining := #[]
      /- Solving one pure goal may instantiate metavariables and thereby close
      another generated goal. Check liveness immediately before invoking the
      solver, rather than taking one stale snapshot for the entire batch. -/
      for goal in generated do
        if ← goal.isAssignedOrDelayedAssigned then continue
        try
          let produced ← withSuppressedMessages <| evalTacticAt input.config.pureSolver goal
          Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
          remaining := remaining ++ (← openGoals produced)
        catch exception =>
          trace[ibubble.rule] "pure solver failed: {exception.toMessageData}"
          before.restore
          return RuleOutput.ofSpecs #[]
      pure remaining
    if !input.config.pureStop? && !pending.isEmpty then
      before.restore
      return RuleOutput.ofSpecs #[]
    return .ofEffect (← Meta.saveState) {}
  catch exception =>
    trace[ibubble.rule] "ipureintro failed: {exception.toMessageData}"
    before.restore
    return RuleOutput.ofSpecs #[]

end Bubble.Tactic.IPureIntro
