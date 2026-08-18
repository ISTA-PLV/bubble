module

public meta import Bubble.Core.Meta

public meta section

open Lean Lean.Meta Iris.ProofMode

namespace Bubble

structure JoinCandidate where
  /- Final bubble of a completed residual-group chain. -/
  bubble : BubbleId
  /- Spatial footprint of the completed group. -/
  consumed : Array IrisHyp
  /- Compatible metavariable assignments accumulated by the group. -/
  metaInfo : Array MetaAssignment
  deriving Inhabited

/- A compatible, complete platform selection ready to rise through its Rapp. -/
structure JoinEmission where
  bubbles : Array BubbleId
  consumed : Array IrisHyp
  metaInfo : Array MetaAssignment
  deriving Inhabited

structure EmissionKey where
  /- Canonical spatial footprint of the emitted proof. -/
  consumed : Array IVarId
  /- Canonical metavariable assignments carried by the emitted proof. -/
  metaInfo : Array (MVarId × ExprStructEq)
  deriving BEq, Hashable

structure Join where
  roots : Array GroupId
  candidates : Std.HashMap GroupId $ Array JoinCandidate := {}
  /- Suppress emissions carrying the same spatial and metavariable information. -/
  emitted : Std.HashSet EmissionKey := default
  deriving Inhabited

namespace Join

private def sameResource (left right : IrisHyp) : Bool :=
  left.ivar == right.ivar

/-- Construct an order-independent key from an emission's semantic content. -/
private def emissionKey (consumed : Array IrisHyp)
    (metaInfo : Array MetaAssignment) : EmissionKey := {
  consumed := (consumed.map (·.ivar)).qsort λ left right =>
    Name.quickCmp left.name right.name == .lt
  metaInfo := (metaInfo.map λ assignment =>
    (assignment.mvarId, ⟨assignment.value⟩)).qsort λ left right =>
      Name.quickCmp left.1.name right.1.name == .lt
}

/-- Combine two candidate footprints according to the platform policy. -/
def appendResources (kind : PlatKind)
    (left right : Array IrisHyp) : Option (Array IrisHyp) :=
  if kind.isLinear && left.any λ used => right.any (sameResource used) then
    none
  else
    some <| right.foldl (init := left) λ resources used =>
      if resources.any (sameResource used) then resources else resources.push used

/--
  Register one completed group chain, emit every newly enabled compatible
  platform selection, and record those emissions atomically.
-/
def registerCandidate (join : Join) (kind : PlatKind) (baseState : SavedState)
    (root : GroupId) (candidate : JoinCandidate) :
    MetaM (Join × Array JoinEmission) := do
  let previous := join.candidates[root]?.getD #[]
  if previous.any (·.bubble == candidate.bubble) then
    throwError "ibubble (join): terminal bubble {candidate.bubble} is already registered for root group {root}"
  let some arrivingIdx := join.roots.findIdx? (· == root)
    | throwError "ibubble (join): unknown root group {root}"

  /- Register the candidate into the join. -/
  let join := { join with candidates := join.candidates.insert root (previous.push candidate) }
  let choices := join.roots.map (join.candidates[·]?.getD #[])
  if choices.any (·.isEmpty) then return (join, #[])

  /- Try to combine with other root group candidates to have new emission. -/
  let selections := (choices.mapIdx λ idx alternatives =>
      if idx == arrivingIdx then #[candidate] else alternatives).foldl
    (init := #[#[]]) λ selections alternatives =>
      selections.foldl (init := #[]) λ next selection =>
        alternatives.foldl (init := next) λ next alternative =>
          next.push (selection.push alternative)

  /- Emit each new compatible semantic selection at most once. -/
  selections.foldlM (init := (join, #[])) λ (join, emissions) selected => do
    let some consumed := selected.foldl (init := some #[]) λ accumulated candidate =>
      accumulated.bind λ consumed => appendResources kind consumed candidate.consumed
    | return (join, emissions)
    let some metaInfo ← Bubble.Meta.mergeMetaInfo baseState (selected.map (·.metaInfo))
      | return (join, emissions)
    let key := emissionKey consumed metaInfo
    if join.emitted.contains key then return (join, emissions)
    return ({ join with emitted := join.emitted.insert key }, emissions.push {
      bubbles := selected.map (·.bubble)
      consumed
      metaInfo
    })

end Join

end Bubble
