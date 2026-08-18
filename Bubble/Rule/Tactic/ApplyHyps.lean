module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.ApplyHyps

open Lean Meta Qq
open Iris.BI
open Iris.ProofMode

private structure Expansion where
  usedHyp : AppliedHyp
  goals : Array SubGoal
  postState : Meta.SavedState

/- Extract a rigid conclusion for cheaply filtering common hypothesis shapes. -/
private partial def candidateConclusion? (type : Expr) : MetaM (Option Expr) := do
  let type := (← instantiateMVars type).consumeMData
  if let some args := type.appM? ``BIBase.wand then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.imp then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.intuitionistically then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.affinely then
    let some target := args.back? | return none
    candidateConclusion? target
  else if let some args := type.appM? ``BIBase.persistently then
    let some target := args.back? | return none
    candidateConclusion? target
  else if type.isAppOfArity ``BIBase.and 4 || type.isAppOfArity ``BIBase.or 4 ||
      type.isAppOfArity ``BIBase.sep 4 || type.isAppOf ``BIBase.later ||
      type.isAppOf ``BIBase.forall || type.isAppOf ``BIBase.exists then
    return none
  else
    return some type

/- Reject only conclusions headed by distinct rigid constants. -/
private def conclusionMatches? (conclusion target : Expr) : MetaM Bool := do
  if !(← getMVars conclusion).isEmpty || !(← getMVars target).isEmpty then return true
  let defEq ← withoutModifyingState do
    try isDefEq conclusion target
    catch _ => return false
  if defEq then return true
  match conclusion.consumeMData.getAppFn.constName?,
      target.consumeMData.getAppFn.constName? with
  | some left, some right =>
      return left == right || (← isProjectionFn left) || (← isProjectionFn right)
  | _, _ => return true

/- Check whether an Iris hypothesis can possibly conclude the current target. -/
private def irisCandidateCouldMatch (type target : Expr) : MetaM Bool := do
  let some conclusion ← candidateConclusion? type | return true
  conclusionMatches? conclusion target

/- Check whether a bridged Lean proposition can possibly conclude the target. -/
private def leanCandidateCouldMatch (type target : Expr) : MetaM Bool := do
  let type := type.consumeMData
  let target? :=
    (type.appM? ``BIBase.Entails <|> type.appM? ``BIBase.EmpValid <|>
      type.appM? ``BIBase.BiEntails).bind Array.back?
  let some candidateTarget := target? | return true
  let some conclusion ← candidateConclusion? candidateTarget | return true
  conclusionMatches? conclusion target

private def closeWithHyp?
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (usedHyp : AppliedHyp) (persistent : Q(Bool))
    (hypType target : Q($prop)) : MetaM (Option Expansion) := do
  let hypType : Q($prop) ← instantiateMVars hypType
  let target : Q($prop) ← instantiateMVars target
  let before ← Meta.saveState
  match ← Tactic.trySynthInstanceProbeQ
      q(FromAssumption $persistent .in $hypType $target) with
  | .none | .undef => before.restore; return none
  | .some _ =>
      let _ ← instantiateMVars hypType
      let _ ← instantiateMVars target
      return some {
        usedHyp, goals := #[], postState := ← Meta.saveState
      }

private partial def collectPremises?
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (persistent : Q(Bool)) (hypType target : Q($prop)) :
    MetaM (Option (Array Q($prop))) := do
  let hypType : Q($prop) ← instantiateMVars hypType
  let target : Q($prop) ← instantiateMVars target
  let before ← Meta.saveState
  let premise ← mkFreshExprMVarQ prop
  match ← Tactic.trySynthInstanceProbeQ
      q(IntoWand $persistent false $hypType (.matching .result) $premise $target) with
  | .some _ =>
      let premise : Q($prop) ← instantiateMVars premise
      return some #[premise]
  | .none | .undef => before.restore
  let premise ← mkFreshExprMVarQ prop
  let rest ← mkFreshExprMVarQ prop
  match ← Tactic.trySynthInstanceProbeQ
      q(IntoWand $persistent false $hypType .unknown $premise $rest) with
  | .none | .undef => before.restore; return none
  | .some _ =>
      let premise : Q($prop) ← instantiateMVars premise
      let rest : Q($prop) ← instantiateMVars rest
      match ← collectPremises? (bi := bi) q(false) rest target with
      | none => before.restore; return none
      | some premises =>
          let premises : Array Q($prop) ← premises.mapM instantiateMVars
          return some (#[premise] ++ premises)

private def mkChildren (irisGoal : IrisGoal) (tag : Name)
    {e' : Q($irisGoal.prop)} (hyps : Hyps irisGoal.bi e')
    (premises : Array Q($irisGoal.prop)) :
    MetaM (Array SubGoal) := do
  premises.foldlM (init := #[]) fun goals premise => do
    let premise : Q($irisGoal.prop) ← instantiateMVars premise
    let template := { irisGoal with e := e', hyps, goal := premise }
    let child ← mkFreshExprSyntheticOpaqueMVar template.toExpr tag
    return goals.push (← SubGoal.ofMVar child.mvarId!)

private partial def collectFromIris
    {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (irisGoal : IrisGoal) (tag : Name) (baseState : Meta.SavedState) :
    ∀ {e}, Hyps bi e → MetaM (Array Expansion × Array Expansion)
  | _, .emp _ => return (#[], #[])
  | _, .sep _ _ _ _ left right => do
      let (leftClose, leftApply) ← collectFromIris irisGoal tag baseState left
      let (rightClose, rightApply) ← collectFromIris irisGoal tag baseState right
      return (leftClose ++ rightClose, leftApply ++ rightApply)
  | _, .hyp _ name ivar persistent hypType _ => do
      baseState.restore
      let instantiated : Q($prop) ← instantiateMVars hypType
      if (← getMVars instantiated).isEmpty then
        if let .defEq _ ← isDefEqQ instantiated q(iprop(False)) then
          return (#[], #[])
      unless ← irisCandidateCouldMatch hypType irisGoal.goal do
        baseState.restore
        return (#[], #[])
      let usedHyp : AppliedHyp :=
        if Iris.ProofMode.isTrue persistent then .intuitionistic { name, ivar }
        else .spatial { name, ivar }
      let close? ← closeWithHyp? (bi := bi) usedHyp persistent hypType irisGoal.goal
      baseState.restore
      let mut apply := #[]
      if let some premises ← collectPremises? (bi := bi)
          persistent hypType irisGoal.goal then
        let some ⟨_, _, remaining, _, _, _, _, _⟩ ←
            irisGoal.hyps.removeG false fun _ candidate _ _ =>
              return if candidate == ivar then some () else none
          | throwError "ibubble: selected Iris hypothesis disappeared"
        let goals ← mkChildren irisGoal tag remaining premises
        apply := apply.push {
          usedHyp, goals, postState := ← Meta.saveState
        }
      baseState.restore
      return (close?.toArray, apply)

private def collectFromLean (irisGoal : IrisGoal) (tag : Name)
    (baseState : Meta.SavedState) : MetaM (Array Expansion) := do
  let { prop, bi, goal := target, .. } := irisGoal
  let mut closeExpansions := #[]
  let mut applyExpansions := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    baseState.restore
    let type ← instantiateMVars decl.type
    unless ← Meta.isProp type do continue
    have type : Q(Prop) := type
    unless ← leanCandidateCouldMatch type target do continue
    let hyp ← mkFreshExprMVarQ prop
    let .some _ ← Tactic.trySynthInstanceProbeQ
        q(AsEmpValid .into $type .in $prop $bi $hyp)
      | continue
    let hyp : Q($prop) ← instantiateMVars hyp
    let bridgedState ← Meta.saveState
    let usedHyp := AppliedHyp.lean decl.userName decl.fvarId
    if let some expansion ← closeWithHyp? (bi := bi) usedHyp q(true) hyp target then
      closeExpansions := closeExpansions.push expansion
    bridgedState.restore
    if let some premises ← collectPremises? (bi := bi) q(true) hyp target then
      let goals ← mkChildren irisGoal tag irisGoal.hyps premises
      applyExpansions := applyExpansions.push {
        usedHyp, goals, postState := ← Meta.saveState
      }
  baseState.restore
  return closeExpansions ++ applyExpansions

def run (input : RuleInput) : Lean.Elab.Tactic.TacticM RuleOutput := do
  input.state.restore
  input.goal.withContext do
    let some irisGoal ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
    let tag ← input.goal.getTag
    let baseState ← Meta.saveState
    let (irisClose, irisApply) ←
      collectFromIris irisGoal tag baseState irisGoal.hyps
    let expansions := irisClose ++ irisApply ++
      (← collectFromLean irisGoal tag baseState)
    return .ofSpecs <| expansions.map fun expansion => {
      goals := expansion.goals
      postState := expansion.postState
      effect := {
        usedHyps := #[expansion.usedHyp]
        multiGoalAction? :=
          if expansion.goals.size > 1 then some .partitionContext else none
      }
    }

end Bubble.Rule.Tactic.ApplyHyps
