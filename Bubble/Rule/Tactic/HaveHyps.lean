-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Tactic.HaveHyps

open Lean Meta Qq
open Iris.ProofMode
open Bubble.Search

private structure Expansion where
  usedHyp : AppliedHyp
  generatedHyp? : Option IrisHyp
  goals : Array SubGoal
  postState : Meta.SavedState

private partial def parseHypothesis?
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (persistent : Q(Bool)) (hyp : Q($prop)) :
    MetaM (Option (Array Q($prop) × Q($prop))) := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let before ← Meta.saveState
  let premise ← mkFreshExprMVarQ prop
  let rest ← mkFreshExprMVarQ prop
  let .some _ ← Tactic.trySynthInstanceProbeQ
      q(IntoWand $persistent false $hyp .unknown $premise $rest)
    | before.restore; return none
  let premise : Q($prop) ← instantiateMVars premise
  let rest : Q($prop) ← instantiateMVars rest
  match ← parseHypothesis? (bi := bi) q(false) rest with
  | some (premises, conclusion) => return some (#[premise] ++ premises, conclusion)
  | none => return some (#[premise], rest)

private def usefulConclusion
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (hyp : Q($prop)) : MetaM Bool := do
  let hyp : Q($prop) ← instantiateMVars hyp
  let before ← Meta.saveState
  let level ← mkFreshLevelMVar
  let α ← mkFreshExprMVarQ q(Sort level)
  let predicate ← mkFreshExprMVarQ q($α → $prop)
  match ← Tactic.trySynthInstanceProbeQ q(IntoExists $hyp $predicate) with
  | .some _ => before.restore; return true
  | .none | .undef => before.restore
  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  match ← Tactic.trySynthInstanceProbeQ q(IntoSep $hyp $left $right) with
  | .some _ => before.restore; return true
  | .none | .undef => before.restore
  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  match ← Tactic.trySynthInstanceProbeQ q(IntoOr $hyp $left $right) with
  | .some _ => before.restore; return true
  | .none | .undef => before.restore
  let prop' ← mkFreshExprMVarQ q(Type u)
  let bi' ← mkFreshExprMVarQ q(Iris.BI $prop')
  let Φ ← mkFreshExprMVarQ q(Prop)
  let M ← mkFreshExprMVarQ q(Modality $prop' $prop)
  let α : Q(Type u) ← mkFreshExprMVarQ q(Type u)
  let selection ← mkFreshExprMVarQ q($α)
  let inner ← mkFreshExprMVarQ q($prop')
  match ← Tactic.trySynthInstanceProbeQ
      q(@FromModal .out $prop' $prop $α $bi' $bi $M $Φ $selection $hyp $inner) with
  | .some _ => before.restore; return true
  | .none | .undef => before.restore
  let inner ← mkFreshExprMVarQ prop
  match ← Tactic.trySynthInstanceProbeQ q(IntoExcept0 $hyp $inner) with
  | .some _ => before.restore; return true
  | .none | .undef => before.restore; return false

private def mkChildren (irisGoal : IrisGoal) (tag : Name) (depth : Nat)
    {e' : Q($irisGoal.prop)} (hyps : Hyps irisGoal.bi e')
    (premises : Array Q($irisGoal.prop)) (conclusion : Q($irisGoal.prop)) :
    MetaM (Array SubGoal × Option IrisHyp) := do
  let goals ← premises.foldlM (init := #[]) fun goals premise => do
    let premise : Q($irisGoal.prop) ← instantiateMVars premise
    let template := { irisGoal with e := e', hyps, goal := premise }
    let child ← mkFreshExprSyntheticOpaqueMVar template.toExpr tag
    return goals.push (← SubGoal.ofMVar child.mvarId!)
  let conclusion : Q($irisGoal.prop) ← instantiateMVars conclusion
  let binder ← mkFreshBinderFromNames (hypNames irisGoal.hyps) depth
  let (name, _) ← getFreshName binder
  let ivar ← mkFreshIVarId false
  let ⟨extendedExpr, extended, _⟩ :=
    Hyps.add irisGoal.bi name ivar q(false) conclusion hyps
  let template := { irisGoal with e := extendedExpr, hyps := extended }
  let child ← mkFreshExprSyntheticOpaqueMVar template.toExpr tag
  return (
    goals.push (← SubGoal.ofMVar child.mvarId!),
    if ivar.persistent? then none else some { name, ivar })

private partial def collect
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (depth : Nat)
    (baseState : Meta.SavedState) :
    ∀ {e}, Hyps bi e → MetaM (Array Expansion)
  | _, .emp _ => return #[]
  | _, .sep _ _ _ _ left right => do
      return (← collect irisGoal tag depth baseState left) ++
        (← collect irisGoal tag depth baseState right)
  | _, .hyp _ name ivar persistent type _ => do
      baseState.restore
      let mut result := #[]
      if let some (premises, conclusion) ← parseHypothesis? (bi := bi) persistent type then
        if !premises.isEmpty && (← usefulConclusion (bi := bi) conclusion) then
          let selected : IrisHyp := { name, ivar }
          let usedHyp : AppliedHyp :=
            if Iris.ProofMode.isTrue persistent then .intuitionistic selected else .spatial selected
          let some ⟨_, _, remaining, _, _, _, _, _⟩ ←
              irisGoal.hyps.removeG true fun _ candidate _ _ =>
                return if candidate == ivar then some () else none
            | throwError "ibubble: haveHyps candidate disappeared"
          let (goals, generatedHyp?) ←
            mkChildren irisGoal tag depth remaining premises conclusion
          result := result.push {
            usedHyp, generatedHyp?, goals, postState := ← Meta.saveState
          }
      baseState.restore
      return result

def run (input : RuleInput) : Lean.Elab.Tactic.TacticM RuleOutput := do
  input.state.restore
  input.goal.withContext do
    let some irisGoal ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
    let expansions ← collect irisGoal (← input.goal.getTag) input.depth
      (← Meta.saveState) irisGoal.hyps
    return .ofSpecs <| expansions.map fun expansion => {
      goals := expansion.goals
      postState := expansion.postState
      effect := {
        usedHyps := #[expansion.usedHyp]
        generatedSpatialHyps := expansion.generatedHyp?.toArray
        multiGoalAction? := some .partitionContext
      }
    }

end Bubble.Tactic.HaveHyps
