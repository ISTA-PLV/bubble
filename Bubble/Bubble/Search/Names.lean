-- SPDX-License-Identifier: Apache-2.0
module

public meta import Iris.ProofMode.Expr
public meta import Bubble.Core.Types

public meta section

namespace Bubble.Search

open Lean Meta Qq
open Iris.BI Iris.ProofMode

partial def hypNames : ∀ {prop : Q(Type u)} {bi : Q(Iris.BI $prop)} {e},
    Hyps bi e → Array Name
  | _, _, _, .emp _ => #[]
  | _, _, _, .hyp _ name _ _ _ _ => #[name]
  | _, _, _, .sep _ _ _ _ left right => hypNames left ++ hypNames right

partial def spatialHypEntries :
    ∀ {prop : Q(Type u)} {bi : Q(Iris.BI $prop)} {e},
      Hyps bi e → Array (Name × IVarId × Expr)
  | _, _, _, .emp _ => #[]
  | _, _, _, .hyp _ name ivar persistent type _ =>
      if isTrue persistent then #[] else #[(name, ivar, type)]
  | _, _, _, .sep _ _ _ _ left right =>
      spatialHypEntries left ++ spatialHypEntries right

def collectIrisHypNames (goal : MVarId) : MetaM (Array Name) :=
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType | return #[]
    return hypNames irisGoal.hyps

/-- User-facing names already present in the Lean context. Generated scripts
must not shadow these names because later residual proofs may refer to them. -/
def collectLocalUserNames (goal : MVarId) : MetaM (Array Name) :=
  goal.withContext do
    let mut names := #[]
    for localDecl in ← getLCtx do
      let name := localDecl.userName.eraseMacroScopes
      unless name.isAnonymous do
        names := names.push name
    return names

/-- Extract the spatial Iris hypotheses from a proof-mode goal. -/
def spatialHypsOf (goal : MVarId) : MetaM (Array IrisHyp) :=
  goal.withContext do
    let goalType ← instantiateMVars (← goal.getType)
    let some irisGoal := parseIrisGoal? goalType
      | throwError "ibubble: expected an Iris proof-mode goal"
    return (spatialHypEntries irisGoal.hyps).map fun (name, ivar, _) =>
      { name, ivar }

def nameDepthIndexWithPrefix? (pref : String) (name : Name) :
    Option (Nat × Nat) :=
  match name.eraseMacroScopes with
  | .str _ string =>
      match string.splitOn "_" with
      | depthPart :: indexPart :: [] =>
          match depthPart.dropPrefix? pref, indexPart.toNat? with
          | some depthPart, some index =>
              depthPart.toNat?.map fun depth => (depth, index)
          | _, _ => none
      | _ => none
  | _ => none

def mkFreshBinderFromNamesWithPrefix
    (pref : String) (names : Array Name) (depth : Nat)
    (offset : Nat := 1) : MetaM (TSyntax ``binderIdent) := do
  let maxIndex := names.foldl (init := 0) fun current name =>
    match nameDepthIndexWithPrefix? pref name with
    | some (nameDepth, index) =>
        if nameDepth == depth then max current index else current
    | none => current
  let ident := mkIdent <| (Name.mkSimple pref).appendAfter
    s!"{depth}_{maxIndex + offset}"
  `(binderIdent| $ident:ident)

def mkFreshBinderFromNames (names : Array Name) (depth : Nat)
    (offset : Nat := 1) : MetaM (TSyntax ``binderIdent) :=
  mkFreshBinderFromNamesWithPrefix "H" names depth offset

def mkFreshLeanBinderFromNames (names : Array Name) (depth : Nat)
    (offset : Nat := 1) : MetaM (TSyntax ``binderIdent) :=
  mkFreshBinderFromNamesWithPrefix "h" names depth offset

def mkBinderFromName (name : Name) : MetaM (TSyntax ``binderIdent) := do
  let ident := mkIdent name.eraseMacroScopes
  `(binderIdent| $ident:ident)

/-- Match an Iris forall and return its optional binder name. -/
def matchForall? (target : Expr) : MetaM (Option (Option Name)) := do
  let target := target.consumeMData
  if target.getAppFn.constName? != some ``BIBase.forall then return none
  let some argument := target.getAppArgs.back?
    | throwError "ibubble: malformed Iris forall without a predicate"
  match argument.consumeMData with
  | .lam name .. =>
      let name := name.eraseMacroScopes
      if name.isAnonymous then return some none
      return some (some name)
  | _ => throwError "ibubble: malformed Iris forall predicate; expected a lambda"

end Bubble.Search
