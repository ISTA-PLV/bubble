-- SPDX-License-Identifier: Apache-2.0
module

public meta import Iris.ProofMode.Tactics.Intro
public meta import Bubble.Search.Normalization.Basic

public meta section

namespace Bubble.Search.Normalization

open Lean Lean.Meta Elab Tactic
open Iris.BI Iris.ProofMode

private def mkIntroTactic (pattern : IntroPat) : MetaM (TSyntax `tactic) :=
  match pattern with
  | .intro casesPattern => do
      let casesPattern ← renderICasesPat casesPattern
      `(tactic| iintro $casesPattern:icasesPat)
  | .modintro => `(tactic| iintro !>)
  | _ => throwError "ibubble: unsupported normalization intro script"

private def runIntroPat (goal : MVarId) (pattern : IntroPat) :
    TacticM StepResult := do
  runTactic goal (← mkIntroTactic pattern)

/-- Introduce a persistent modality when it immediately encloses an Iris forall. -/
private def persistIntro? (goal : MVarId) : TacticM (Option StepResult) := do
  let applicable ← liftM (m := MetaM) <| goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType | return false
    let target := irisGoal.goal.consumeMData
    let modality := target.getAppFn.constName?
    if modality != some ``Iris.BI.intuitionistically then
      return false
    let some inner := target.getAppArgs.back? | return false
    return inner.consumeMData.getAppFn.constName? == some ``BIBase.forall
  if !applicable then return none
  return some (← runIntroPat goal .modintro)

def introStep : Step where
  label := "intro"
  run input := do
    if let some result ← persistIntro? input.goal then
      return result
    let names := (← collectIrisHypNames input.goal) ++
      (← collectLocalUserNames input.goal)

    /- Introduce an Iris forall binder as a pure Lean variable. -/
    let forallBinder? ← input.goal.withContext do
      let goalType ← instantiateMVars (← input.goal.getType)
      let some irisGoal := parseIrisGoal? goalType | return none
      matchForall? irisGoal.goal
    if let some binderName? := forallBinder? then
      let name ← match binderName? with
        | some name =>
            let name := name.eraseMacroScopes
            if names.contains name then
              mkFreshLeanBinderFromNames names input.depth
            else
              mkBinderFromName name
        | none => mkFreshLeanBinderFromNames names input.depth
      let pattern ← parseICasesPat <| ← mkPurePatSyntax name
      return ← runIntroPat input.goal (.intro pattern)

    /- Primary case -/
    let name ← mkFreshBinderFromNames names input.depth
    let pattern ← parseICasesPat <| ← mkOnePatSyntax name
    runIntroPat input.goal (.intro pattern)

end Bubble.Search.Normalization
