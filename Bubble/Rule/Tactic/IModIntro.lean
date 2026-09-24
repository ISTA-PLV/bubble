-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.IModIntro

open Lean Elab Tactic Meta
open Iris.ProofMode

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let some pre ← Tactic.irisGoal? input.goal | return .ofSpecs #[]
  let before ← Tactic.saveState
  try
    let tactic ← `(tactic| imodintro)
    let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
    let some child ← generated.findM? λ goal => do
        if ← goal.isAssignedOrDelayedAssigned then return false
        return (← Tactic.irisGoal? goal).isSome
      | before.restore; return .ofSpecs #[]
    let some post ← Tactic.irisGoal? child
      | before.restore; return .ofSpecs #[]
    let (consumed, generated) ← Tactic.spatialDiff pre post
    let child ← SubGoal.ofMVar child
    return .ofSpec {
      goals := #[child]
      postState := ← Meta.saveState
      effect := {
        usedHyps := consumed.map .spatial
        generatedSpatialHyps := generated
      }
    }
  catch _ =>
    before.restore
    return .ofSpecs #[]

end Bubble.Rule.Tactic.IModIntro
