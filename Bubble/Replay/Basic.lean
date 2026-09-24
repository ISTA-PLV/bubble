-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean.Elab.Tactic
public meta import Lean.Meta.Tactic.TryThis
public import Batteries.Tactic.PermuteGoals
public meta import Batteries.Lean.Meta.SavedState

public meta section

open Lean Lean.Meta Lean.Elab.Tactic
open Lean.Parser.Tactic (tacticSeq)

namespace Bubble

private def mkOneBasedNumLit (n : Nat) : NumLit :=
  Syntax.mkNumLit $ toString $ n + 1

private def mkPickGoal (goalPos : Nat) : MetaM (TSyntax `tactic) := do
  let posLit := mkOneBasedNumLit goalPos
  `(tactic| pick_goal $posLit:num)

private def mkRotateLeft (n : Nat) : MetaM (TSyntax `tactic) := do
  if n == 1 then
    `(tactic| rotate_left)
  else
    let nLit : NumLit := Syntax.mkNumLit (toString n)
    `(tactic| rotate_left $nLit:num)

structure ScriptStep where
  preState : Meta.SavedState
  preGoal : MVarId
  tactic : TSyntax `tactic
  postState : Meta.SavedState
  postGoals : Array MVarId

abbrev UScript := Array ScriptStep

structure TacticState where
  goals : Array MVarId

namespace TacticState

private def retainOpen (s : TacticState) (state : Meta.SavedState) : MetaM TacticState :=
  state.runMetaM' do
    return { goals := ← s.goals.filterM λ goal =>
      not <$> goal.isAssignedOrDelayedAssigned }

def getVisibleGoalIndex (s : TacticState) (goal : MVarId) : MetaM Nat := do
  let some idx := s.goals.idxOf? goal
    | throwError "ibubble?: script rendering could not find goal {goal.name}"
  return idx

def pickGoal (s : TacticState) (idx : Nat) : TacticState :=
  if idx == 0 then s
  else match s.goals[idx]? with
    | some goal =>
      { goals := #[goal] ++ s.goals.extract 0 idx ++
          s.goals.extract (idx + 1) s.goals.size }
    | none => s

def rotateLeft (s : TacticState) (n : Nat) : TacticState :=
  if n == 0 || s.goals.isEmpty then s
  else
    let n := n % s.goals.size
    { goals := s.goals.extract n s.goals.size ++ s.goals.extract 0 n }

private def retainOpenCurrent (s : TacticState) : MetaM TacticState := do
  return { goals := ← s.goals.filterM λ goal =>
    not <$> goal.isAssignedOrDelayedAssigned }

/-- Emit a final permutation so that replacing `ibubble?` with its suggestion
leaves residual goals in the same order as the tactic invocation. -/
def renderFinalOrder (s : TacticState) (target : Array MVarId) :
    MetaM (Array (TSyntax `tactic)) := do
  let mut state ← s.retainOpenCurrent
  let target ← target.filterM λ goal =>
    not <$> goal.isAssignedOrDelayedAssigned
  unless state.goals.size == target.size && target.all state.goals.contains do
    throwError "ibubble?: generated script has a different set of residual goals"
  if state.goals == target then return #[]

  /- Prefer one rotation when the residual order differs only cyclically. This
     is the usual `pureStop` case: each `ipureintro` defers one pure goal. -/
  for pos in [1:state.goals.size] do
    if (state.rotateLeft pos).goals == target then
      return #[(← mkRotateLeft pos)]

  /- Fall back to a general permutation by moving target goals to the front in
     reverse order. -/
  let mut tactics := #[]
  for goal in target.reverse do
    /- Residual arrays can contain the same metavariable more than once. Taking
       the last occurrence makes the reverse insertion algorithm stable. -/
    let some reverseIdx := state.goals.reverse.idxOf? goal
      | throwError "ibubble?: generated script could not locate a residual goal"
    let idx := state.goals.size - reverseIdx - 1
    if idx > 0 then
      tactics := tactics.push (← mkPickGoal idx)
      state := state.pickGoal idx
  unless state.goals == target do
    throwError "ibubble?: generated script could not restore residual goal order; got {state.goals.map (·.name)}, expected {target.map (·.name)}"
  return tactics

def applyStepAtHead (s : TacticState) (step : ScriptStep) : TacticState :=
  { goals := step.postGoals ++ s.goals.extract 1 s.goals.size }

def applyStep (s : TacticState) (step : ScriptStep) : MetaM TacticState := do
  let idx ← s.getVisibleGoalIndex step.preGoal
  return (s.pickGoal idx).applyStepAtHead step

end TacticState

namespace ScriptStep

def render (acc : Array (TSyntax `tactic)) (step : ScriptStep)
    (tacticState : TacticState) :
    MetaM (Array (TSyntax `tactic) × TacticState) := do
  /- Metavariable goals can be solved indirectly while replaying a sibling. -/
  let tacticState ← tacticState.retainOpen step.preState
  let pos ← tacticState.getVisibleGoalIndex step.preGoal
  let focusTactic? ←
    if pos == 0 then
      pure none
    else if pos + 1 == tacticState.goals.size then
      pure (some (← mkRotateLeft pos))
    else
      pure (some (← mkPickGoal pos))
  let tacticState ← tacticState.applyStep step
  let acc := focusTactic?.elim acc acc.push
  return (acc.push step.tactic, tacticState)

end ScriptStep

namespace UScript

def render (s : UScript) (rootGoal : MVarId)
    (finalGoals? : Option (Array MVarId) := none) :
    MetaM (Array (TSyntax `tactic)) := do
  let mut script := Array.mkEmpty s.size
  let mut tacticState : TacticState := { goals := #[rootGoal] }
  for step in s do
    let (script', tacticState') ← step.render script tacticState
    script := script'
    tacticState := tacticState'
  if let some finalGoals := finalGoals? then
    script := script ++ (← tacticState.renderFinalOrder finalGoals)
  return script

def renderTacticSeq (s : UScript) (rootGoal : MVarId)
    (finalGoals? : Option (Array MVarId) := none) :
    MetaM (TSyntax ``tacticSeq) := do
  `(tacticSeq| $(← s.render rootGoal finalGoals?):tactic*)

end UScript

def addTryThisTacticSeqSuggestion (ref : Syntax)
    (tacs : Array (TSyntax `tactic)) : MetaM Unit := do
  let map ← getFileMap
  let col := match ref.getPos? with
    | some pos => (map.toPosition pos).column
    | none => 0
  let width := Lean.Meta.Tactic.TryThis.getInputWidth (← getOptions)
  let lineStrs ← tacs.mapM fun t => do
    let fmt ← PrettyPrinter.ppTactic t
    pure <| fmt.pretty (width := width) (indent := col) (column := col)
  let pad := "\n".pushn ' ' col
  let msgText := String.intercalate pad lineStrs.toList
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string msgText
    toCodeActionTitle? := some λ _ => "Replace ibubble? with the proof it found"
    messageData? := some msgText
  }
  Lean.Meta.Tactic.TryThis.addSuggestion ref suggestion (header := "Try this:\n")

end Bubble
