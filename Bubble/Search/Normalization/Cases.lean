-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Search.Normalization.Basic

public meta section

namespace Bubble.Search.Normalization

open Lean Lean.Meta Qq Elab Tactic
open Iris.BI Iris.ProofMode

private structure NormHyp where
  name : Name
  persistent : Expr
  type : Expr

private partial def collectNormHyps {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array NormHyp
  | _, .emp _ => #[]
  | _, .hyp _ name _ persistent type _ => #[{ name, persistent, type }]
  | _, .sep _ _ _ _ left right => collectNormHyps left ++ collectNormHyps right

private def mkICasesTactic (hyp : Name) (pattern : iCasesPat) :
    MetaM (TSyntax `tactic) := do
  let pattern ← renderICasesPat pattern
  let hyp := mkIdent hyp
  `(tactic| icases $hyp:term with $pattern:icasesPat)

private def mkPairPatSyntax (left right : TSyntax ``binderIdent) :
    MetaM (TSyntax `icasesPat) :=
  `(icasesPat| ⟨$left:binderIdent, $right:binderIdent⟩)

private def mkExistsPatSyntax (witness body : TSyntax ``binderIdent) :
    MetaM (TSyntax `icasesPat) := do
  let witnessPat ← mkPurePatSyntax witness
  let bodyPat ← mkOnePatSyntax body
  let witnessAlt ← `(icasesPatAlts| $witnessPat:icasesPat)
  let bodyAlt ← `(icasesPatAlts| $bodyPat:icasesPat)
  let alternatives := #[witnessAlt, bodyAlt]
  `(icasesPat| ⟨$alternatives,*⟩)

private def mkIntuitionisticPatSyntax (name : TSyntax ``binderIdent) :
    MetaM (TSyntax `icasesPat) := do
  let inner ← mkOnePatSyntax name
  `(icasesPat| #$inner:icasesPat)

private def firstSuccessfulCasesStep (goal : MVarId)
    (hyps : Array NormHyp) (pattern : iCasesPat)
    (eligible : NormHyp → MetaM Bool) : TacticM (Option StepResult) := do
  hyps.findSomeM? fun hyp => do
    let isEligible ← liftM (m := MetaM) do
      try
        let state ← saveState
        state.runMetaM' <| goal.withContext <| eligible hyp
      catch _ => return false
    if !isEligible then return none
    tryAttempt <| runTactic goal (← mkICasesTactic hyp.name pattern)

private def canExists {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (hyp : NormHyp) : MetaM Bool := do
  let type ← instantiateMVars hyp.type
  let some irisType ← checkTypeQ type prop | return false
  let v ← mkFreshLevelMVar
  let α : Q(Sort v) ← mkFreshExprMVarQ q(Sort v)
  let predicate : Q($α → $prop) ← mkFreshExprMVarQ q($α → $prop)
  match ← Iris.ProofMode.trySynthInstanceQ q(IntoExists $irisType $predicate) with
  | .some _ => return true
  | _ => return false

private def canSplitSep (hyp : NormHyp) : MetaM Bool := do
  let type ← instantiateMVars hyp.type
  let target := type.consumeMData
  if target.getAppFn.constName? != some ``BIBase.sep then return false
  return target.getAppArgs.size >= 3

private def canSplitConjLike {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (hyp : NormHyp) : MetaM Bool := do
  let type : Q($prop) ← instantiateMVars hyp.type
  let some persistent ← checkTypeQ hyp.persistent q(Bool) | return false
  if !isTrue persistent then return false
  let left ← mkFreshExprMVarQ prop
  let right ← mkFreshExprMVarQ prop
  match ← Iris.ProofMode.trySynthInstanceQ q(IntoAnd true $type $left $right) with
  | .some _ => return true
  | _ => return false

private def canPure {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (hyp : NormHyp) : MetaM Bool := do
  let type ← instantiateMVars hyp.type
  let some irisType ← checkTypeQ type prop | return false
  if (← getMVars irisType).isEmpty then
    if let .defEq _ ← isDefEqQ irisType q(iprop(False)) then return false
  let proposition ← mkFreshExprMVarQ q(Prop)
  match ← Iris.ProofMode.trySynthInstanceQ q(IntoPure $irisType $proposition) with
  | .some _ => return true
  | _ => return false

private def canIntuitionistic {u : Level} {prop : Q(Type u)} {bi : Q(Iris.BI $prop)}
    (hyp : NormHyp) : MetaM Bool := do
  if hyp.persistent.constName? != some ``false then return false
  let type ← instantiateMVars hyp.type
  let some irisType ← checkTypeQ type prop | return false
  if (← getMVars irisType).isEmpty then
    if let .defEq _ ← isDefEqQ irisType q(iprop(False)) then return false
  let persistent ← mkFreshExprMVarQ prop
  match ← Iris.ProofMode.trySynthInstanceQ
      q(IntoPersistently false $irisType $persistent) with
  | .some _ => return true
  | _ => return false

def casesStep : Step where
  label := "cases"
  run input := do
    input.goal.withContext do
      let goalType ← instantiateMVars (← input.goal.getType)
      let some irisGoal := parseIrisGoal? goalType | return .unchanged
      let hyps := collectNormHyps irisGoal.hyps
      let names := hyps.map (·.name)

      /- Split Spatial separating conjunctions first -/
      let lhs ← mkFreshBinderFromNames names input.depth
      let rhs ← mkFreshBinderFromNames names input.depth 2
      let pattern ← parseICasesPat <| ← mkPairPatSyntax lhs rhs
      if let some result ← firstSuccessfulCasesStep input.goal hyps pattern canSplitSep then
        return result

      /- Destruct existentials: `icases H with ⟨%x, Hx⟩`. -/
      let witness ← mkFreshLeanBinderFromNames names input.depth
      let body ← mkFreshBinderFromNames names input.depth
      let pattern ← parseICasesPat <| ← mkExistsPatSyntax witness body
      if let some result ← firstSuccessfulCasesStep input.goal hyps pattern
          (canExists  (bi := irisGoal.bi)) then
        return result

      /- Split conjunction-like hypotheses, including iff -/
      let lhs ← mkFreshBinderFromNames names input.depth
      let rhs ← mkFreshBinderFromNames names input.depth 2
      let pattern ← parseICasesPat <| ← mkPairPatSyntax lhs rhs
      if let some result ← firstSuccessfulCasesStep input.goal hyps pattern
          (canSplitConjLike (bi := irisGoal.bi)) then
        return result

      /- Extract pure hypotheses. -/
      let name ← mkFreshBinderFromNames names input.depth
      let pattern ← parseICasesPat <| ← mkPurePatSyntax name
      if let some result ← firstSuccessfulCasesStep input.goal hyps pattern
          (canPure (bi := irisGoal.bi)) then
        return result

      /- Move persistent hypotheses into the intuitionistic context -/
      let name ← mkFreshBinderFromNames names input.depth
      let pattern ← parseICasesPat <| ← mkIntuitionisticPatSyntax name
      return (← firstSuccessfulCasesStep input.goal hyps pattern
        (canIntuitionistic (bi := irisGoal.bi))).getD .unchanged

end Bubble.Search.Normalization
