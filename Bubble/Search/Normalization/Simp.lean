module

public meta import Lean.Elab.Tactic.Simp
public meta import Bubble.Search.Normalization.Basic

public meta section

namespace Bubble.Search.Normalization

open Lean Lean.Meta Elab Tactic

def simpStep : Step where
  label := "simp"
  run input := do
    if !input.enableSimp then return .unchanged
    input.goal.withContext do
      let context := (← Simp.mkContext {} #[← getSimpTheorems]
        <| ← getSimpCongrTheorems).setFailIfUnchanged false
      let (result?, stats) ← Meta.simpAll input.goal context
      let baseTactic ← `(tactic| simp_all)
      let tactic : TSyntax `tactic := ⟨← mkSimpOnly baseTactic stats.usedTheorems⟩
      match result? with
      | none =>
          if !(← input.goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)) then
            return .proved #[] (some tactic)
          return .unchanged
      | some newGoal =>
          if newGoal == input.goal then return .unchanged
          return .changed newGoal #[] (some tactic)

end Bubble.Search.Normalization
