module

public meta import Lean.Elab.Tactic.Simp
public meta import Bubble.Search.Normalization.Basic

public meta section

namespace Bubble.Search.Normalization

open Lean Lean.Meta Elab Tactic

private def runSimpAll (input : StepInput) (context : Simp.Context)
    (simprocs : Simp.SimprocsArray) (baseTactic : TSyntax `tactic) :
    TacticM StepResult := do
  let (result?, stats) ← Meta.simpAll input.goal context simprocs
  let tactic : TSyntax `tactic := ⟨← mkSimpOnly baseTactic stats.usedTheorems⟩
  match result? with
  | none =>
      if !(← input.goalMVars.anyM (notM ·.isAssignedOrDelayedAssigned)) then
        return .proved #[] (some tactic)
      return .unchanged
  | some newGoal =>
      if newGoal == input.goal then return .unchanged
      return .changed newGoal #[] (some tactic)

def simpStep : Step where
  label := "simp"
  run input := do
    if !input.enableSimp then return .unchanged
    input.goal.withContext do
      /- First try the local simp theorem and propositional hypotheses (like `simp_all only`).-/
      let mut simpOnlyThms : SimpTheorems := {}
      for theoremName in simpOnlyBuiltins do
        simpOnlyThms ← simpOnlyThms.addConst theoremName
      let localContext := (← Simp.mkContext {} #[simpOnlyThms]
        <| ← getSimpCongrTheorems).setFailIfUnchanged false
      let beforeLocal ← liftM (m := MetaM) saveState
      let localResult ← runSimpAll input localContext #[{}] (← `(tactic| simp_all only))
      match localResult with
      | .proved .. | .changed .. => return localResult
      | .unchanged => beforeLocal.restore

      /- Fall back to ordinary `simp_all`. -/
      let globalContext := (← Simp.mkContext {} #[← getSimpTheorems]
        <| ← getSimpCongrTheorems).setFailIfUnchanged false
      let globalSimprocs : Simp.SimprocsArray := #[← Simp.getSimprocs]
      runSimpAll input globalContext globalSimprocs (← `(tactic| simp_all))

end Bubble.Search.Normalization
