-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.ICases

open Lean Elab Tactic Meta Qq
open Iris.ProofMode

private structure Candidate where
  name : Name
  applied : AppliedHyp
  type : Expr

private partial def candidates {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array Candidate
  | _, .emp _ => #[]
  | _, .hyp _ name ivar persistent type _ =>
      let hyp : IrisHyp := { name, ivar }
      #[{ name, applied := if Iris.ProofMode.isTrue persistent then
          .intuitionistic hyp else .spatial hyp, type }]
  | _, .sep _ _ _ _ left right => candidates left ++ candidates right

private def openGoals (goals : List MVarId) : MetaM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

private def runOrCandidate (input : RuleInput) (pre : IrisGoal)
    (candidate : Candidate) : TacticM (Option RappSpec) := do
  input.state.restore
  let before ← Tactic.saveState
  let hyp := mkIdent candidate.name
  let left := mkIdent <| Name.mkSimple s!"Hcase{input.depth}L"
  let right := mkIdent <| Name.mkSimple s!"Hcase{input.depth}R"
  try
    let tactic ← `(tactic| icases $hyp:ident with ($left:ident | $right:ident))
    let generated ← openGoals (← withSuppressedMessages <| evalTacticAt tactic input.goal)
    let mut goals := #[]
    let mut generatedHyps := #[]
    for goal in generated do
      let some template ← Tactic.irisGoal? goal
        | before.restore; return none
      goals := goals.push (← SubGoal.ofMVar goal)
      let (_, newHyps) ← Tactic.spatialDiff pre template
      generatedHyps := generatedHyps ++ newHyps
    unless goals.size == 2 do before.restore; return none
    return some {
      goals
      postState := ← Meta.saveState
      effect := {
        usedHyps := #[candidate.applied]
        generatedSpatialHyps := generatedHyps
        multiGoalAction? := some .shareContext
      }
    }
  catch _ =>
    before.restore
    return none

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let some pre ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
  let mut specs := #[]
  for candidate in candidates pre.hyps do
    if let some spec ← runOrCandidate input pre candidate then
      specs := specs.push spec
  return .ofSpecs specs

def runFalse (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let some pre ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
  let { prop, .. } := pre
  let mut specs := #[]
  for candidate in candidates pre.hyps do
    let before ← Tactic.saveState
    try
      input.state.restore
      let type ← instantiateMVars candidate.type
      unless (← getMVars type).isEmpty do
        before.restore
        continue
      let type : Q($prop) := type
      let .defEq _ ← isDefEqQ type q(iprop(False)) | before.restore; continue
      let hyp := mkIdent candidate.name
      let tactic ← `(tactic| icases $hyp:ident with ⟨⟩)
      let generated ← openGoals (← withSuppressedMessages <| evalTacticAt tactic input.goal)
      if generated.isEmpty && (← input.goal.isAssignedOrDelayedAssigned) then
        specs := specs.push {
          goals := #[]
          postState := ← Meta.saveState
          effect := { usedHyps := #[candidate.applied] }
        }
      else before.restore
    catch _ => before.restore
  return .ofSpecs specs

end Bubble.Rule.Tactic.ICases
