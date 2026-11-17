-- SPDX-License-Identifier: Apache-2.0
module

public meta import Std.Data.TreeMap
public meta import Bubble.Index.Basic

public meta section

namespace Bubble

namespace Index

open Lean Lean.Meta
open Iris.ProofMode

initialize registerTraceClass `ibubble.ruleIndex

private abbrev HitMap :=
  Std.TreeMap Rule (Array IndexMatchLocation)
    Rule.compareByPriorityThenName

private inductive QuerySurface
  | fullGoal (e : Expr)
  | target (e : Expr)
  | irisHyp (loc : IndexMatchLocation) (e : Expr)
  | leanHyp (loc : IndexMatchLocation) (e : Expr)
  | unindexed

private partial def collectIrisHyps {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array (IndexMatchLocation × Expr)
  | _, .emp _ => #[]
  | _, .hyp _ name ivarId p type _ =>
    #[(
      .irisHyp name ivarId (isTrue p),
      type
    )]
  | _, .sep _ _ _ _ lhs rhs =>
    collectIrisHyps lhs ++ collectIrisHyps rhs

@[inline]
private def collectSurfaces (mvar : MVarId) (irisGoal : IrisGoal) :
    MetaM (Array QuerySurface) :=
  mvar.withContext do
    let mut surfaces : Array QuerySurface :=
      #[.fullGoal (← mvar.getType), .target irisGoal.goal]
    for (loc, hypType) in collectIrisHyps irisGoal.hyps do
      surfaces := surfaces.push (.irisHyp loc hypType)
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail then
        continue
      surfaces := surfaces.push
        (.leanHyp (.leanHyp localDecl.userName localDecl.fvarId) localDecl.type)
    return surfaces.push .unindexed

@[inline]
private def locationsToSet (locs : Array IndexMatchLocation) :
    Std.HashSet IndexMatchLocation := Id.run do
  let mut result : Std.HashSet IndexMatchLocation := {}
  for loc in locs do
    result := result.insert loc
  return result

@[inline]
private def emptyHitMap : HitMap :=
  Std.TreeMap.empty

@[inline]
private def insertHit (m : HitMap) (rule : Rule)
    (loc : IndexMatchLocation) : HitMap :=
  match m.get? rule with
  | none => m.insert rule #[loc]
  | some locs => m.insert rule (locs.push loc)

@[inline]
private def collectIndexed (tree : DiscrTree Rule) (e : Expr)
    (loc : IndexMatchLocation) (include? : Rule → Bool)
    (m : HitMap) : MetaM HitMap := do
  let e ← instantiateMVars e
  let rules ← getUnify tree e
  return rules.foldl (init := m) λ m rule =>
    if include? rule then insertHit m rule loc else m

@[inline]
private def collectUnindexed (idx : Index)
    (include? : Rule → Bool) (m : HitMap) : HitMap := Id.run do
  let mut result := m
  for rule in idx.unindexed do
    if include? rule then
      result := insertHit result rule .none
  return result

@[inline]
private def collectSurface (idx : Index)
    (include? : Rule → Bool) (m : HitMap) :
    QuerySurface → MetaM HitMap
  | .fullGoal e => collectIndexed idx.byFullGoal e .fullGoal include? m
  | .target e => collectIndexed idx.byTarget e .target include? m
  | .irisHyp loc e => collectIndexed idx.byIrisHyp e loc include? m
  | .leanHyp loc e => collectIndexed idx.byLeanHyp e loc include? m
  | .unindexed => return collectUnindexed idx include? m

@[inline]
private def hitMapToResults (m : HitMap) : Array RuleMatch :=
  let results := m.foldl
    (λ acc rule locations =>
      acc.push { rule, locations := locationsToSet locations })
    (init := Array.mkEmpty m.size)
  results.qsort λ r s =>
    Rule.compareByPriorityThenName r.rule s.rule == .lt

/-- Query an index against all matchable surfaces of an Iris proof-mode goal:
the full Lean goal type, the Iris target, Iris proof-mode hypotheses, Lean local
 hypotheses, and unindexed rules. -/
def query
    (idx : Index) (mvar : MVarId) (irisGoal : IrisGoal)
    (include? : Rule → Bool := λ _ => true) :
    MetaM (Array RuleMatch) := do
  let mut result : HitMap := emptyHitMap
  for surface in ← collectSurfaces mvar irisGoal do
    result ← collectSurface idx include? result surface
  return hitMapToResults result

def queryMVar
    (idx : Index) (mvar : MVarId)
    (include? : Rule → Bool := fun _ => true) :
    MetaM (Array RuleMatch) := do
  mvar.withContext do
    let goalType ← instantiateMVars (← mvar.getType)
    let some irisGoal := parseIrisGoal? goalType
      | return #[]
    query idx mvar irisGoal include?

end Index

end Bubble
