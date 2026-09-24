-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean.Elab.Tactic.Basic
public meta import Batteries.Lean.Meta.SavedState
public meta import Iris.ProofMode.Tactics.Cases
public meta import Bubble.Search.Names

public meta section

namespace Bubble.Search

open Lean Lean.Meta Std Elab Tactic
open Iris.ProofMode

initialize registerTraceClass `ibubble.search.norm

inductive NormSeqResult where
  | proved
  | changed (goal : MVarId)
  | unchanged
  deriving Inhabited

/-- Observe one successful normalization step without coupling search to replay data. -/
abbrev NormStepObserver := Meta.SavedState → MVarId → TSyntax `tactic →
  Meta.SavedState → Array MVarId → TacticM Unit

namespace Normalization

inductive StepResult where
  | proved (remaining : Array MVarId) (tactic? : Option (TSyntax `tactic))
  | changed (goal : MVarId) (remaining : Array MVarId)
      (tactic? : Option (TSyntax `tactic))
  | unchanged

structure StepInput where
  goal : MVarId
  depth : Nat
  enableSimp : Bool
  goalMVars : Std.HashSet MVarId

structure Step where
  label : String
  run : StepInput → TacticM StepResult

/-- Run one normalization attempt, committing success and rolling back failure. -/
def tryAttempt (action : TacticM StepResult) : TacticM (Option StepResult) := do
  let preState ← liftM (m := MetaM) saveState
  try
    match ← action with
    | .unchanged =>
        preState.restore
        return none
    | result => return some result
  catch _ =>
    preState.restore
    return none

def renderICasesPat (pattern : iCasesPat) : MetaM (TSyntax `icasesPat) :=
  return ⟨pattern.ref⟩

def mkOnePatSyntax (name : TSyntax ``binderIdent) :
    MetaM (TSyntax `icasesPat) :=
  `(icasesPat| $name:binderIdent)

def mkPurePatSyntax (name : TSyntax ``binderIdent) :
    MetaM (TSyntax `icasesPat) := do
  let ident ← match name with
    | `(binderIdent| $ident:ident) => pure ident
    | _ => throwError "ibubble: expected a named binder during normalization"
  let pattern ← `(rcasesPat| $ident:ident)
  `(icasesPat| %$pattern:rcasesPat)

def parseICasesPat (stx : TSyntax `icasesPat) : TacticM iCasesPat :=
  Lean.Elab.liftMacroM <| iCasesPat.parse stx

private def partitionGeneratedGoals (goals : Array MVarId) :
    MetaM (Array MVarId × Array MVarId) := do
  goals.foldlM (init := (#[], #[])) fun (iris, lean) goal => do
    let irisGoal? ← goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      return parseIrisGoal? type
    if irisGoal?.isSome then return (iris.push goal, lean)
    return (iris, lean.push goal)

def runTactic (goal : MVarId) (tactic : TSyntax `tactic) :
    TacticM StepResult := do
  let generated ← (← withSuppressedMessages <| evalTacticAt tactic goal).foldlM
    (init := #[]) fun result goal => do
      if ← goal.isAssignedOrDelayedAssigned then return result
      return result.push goal
  let (irisGoals, remaining) ← partitionGeneratedGoals generated
  match irisGoals with
  | #[] => return .proved remaining (some tactic)
  | #[newGoal] => return .changed newGoal remaining (some tactic)
  | _ => throwError
      "ibubble: normalization tactic generated {irisGoals.size} Iris goals; expected at most one"

end Bubble.Search.Normalization
