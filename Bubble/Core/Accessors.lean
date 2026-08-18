module

public meta import Bubble.Core.Impl

public meta section

open Lean Lean.Meta Std

namespace Bubble

namespace Plat

@[inline]
protected def mk : PlatData GoalRef RappRef → Plat :=
  tree.introPlat

instance : Nonempty Plat :=
  ⟨Plat.mk {
    id := .zero
    parent? := none
    goals := #[]
    groups := #[]
    join := { roots := #[] }
    kind := .single
    bubbleToGroup := {}
  }⟩

@[inline]
protected def elim : Plat → PlatData GoalRef RappRef :=
  tree.elimPlat

@[inline]
protected def modify
    (f : PlatData GoalRef RappRef → PlatData GoalRef RappRef)
    (p : Plat) : Plat :=
  Plat.mk <| f p.elim

@[inline] def id (p : Plat) : PlatId := p.elim.id
@[inline] def parent? (p : Plat) : Option RappRef := p.elim.parent?
@[inline] def goals (p : Plat) : Array GoalRef := p.elim.goals
@[inline] def groups (p : Plat) : Array Group := p.elim.groups
@[inline] def join (p : Plat) : Join := p.elim.join
@[inline] def kind (p : Plat) : PlatKind := p.elim.kind
@[inline] def bubbleToGroup (p : Plat) : HashMap BubbleId GroupId := p.elim.bubbleToGroup

@[inline]
def groupForBubble? (bubbleId : BubbleId) (p : Plat) : Option GroupId :=
  p.bubbleToGroup[bubbleId]?

@[inline] def setId (id : PlatId) (p : Plat) : Plat := p.modify fun p => { p with id }
@[inline] def setParent? (parent? : Option RappRef) (p : Plat) : Plat :=
  p.modify fun p => { p with parent? }
@[inline] def setParent (parent : RappRef) (p : Plat) : Plat := p.setParent? (some parent)
@[inline] def setGoals (goals : Array GoalRef) (p : Plat) : Plat :=
  p.modify fun p => { p with goals }
@[inline] def setGroups (groups : Array Group) (p : Plat) : Plat :=
  p.modify fun p => { p with groups }
@[inline] def setJoin (join : Join) (p : Plat) : Plat := p.modify fun p => { p with join }
@[inline] def setKind (kind : PlatKind) (p : Plat) : Plat := p.modify fun p => { p with kind }
@[inline] def setBubbleToGroup
    (bubbleToGroup : HashMap BubbleId GroupId) (p : Plat) : Plat :=
  p.modify fun p => { p with bubbleToGroup }

instance : BEq Plat where
  beq p₁ p₂ := p₁.id == p₂.id

instance : Hashable Plat where
  hash p := hash p.id

end Plat

namespace Goal

@[inline]
protected def mk : GoalData RappRef PlatRef → Goal :=
  tree.introGoal

instance : Nonempty Goal :=
  ⟨Goal.mk Classical.ofNonempty⟩

@[inline]
protected def elim : Goal → GoalData RappRef PlatRef :=
  tree.elimGoal

@[inline]
protected def modify
    (f : GoalData RappRef PlatRef → GoalData RappRef PlatRef)
    (g : Goal) : Goal :=
  Goal.mk <| f g.elim

@[inline] def id (g : Goal) : GoalId := g.elim.id
@[inline] def parent (g : Goal) : PlatRef := g.elim.parent
@[inline] def children (g : Goal) : Array RappRef := g.elim.children
@[inline] def depth (g : Goal) : Nat := g.elim.depth
@[inline] def slot (g : Goal) : GoalSlot := g.elim.slot
@[inline] def pre? (g : Goal) : Option BubbleId := g.elim.pre?
@[inline] def isForcedUnprovable (g : Goal) : Bool := g.elim.isForcedUnprovable
@[inline] def preNormGoal (g : Goal) : MVarId := g.elim.preNormGoal
@[inline] def preNormState (g : Goal) : SavedState := g.elim.preNormState
@[inline] def normalizationState (g : Goal) : NormalizationState := g.elim.normalizationState
@[inline] def unassignedMvars (g : Goal) : HashSet MVarId := g.elim.unassignedMvars
@[inline] def successProbability (g : Goal) : Percent := g.elim.successProbability
@[inline] def addedInIteration (g : Goal) : Iteration := g.elim.addedInIteration
@[inline] def lastExpandedInIteration (g : Goal) : Iteration := g.elim.lastExpandedInIteration
@[inline] def rulesQueue? (g : Goal) : Option RuleQueue := g.elim.rulesQueue?
@[inline] def appendiedGoalId (g : Goal) : Array GoalId := g.elim.appendiedGoalId

@[inline] def rappChildren? (g : Goal) : Option (Array RappRef) := some g.children
@[inline] def hasNoChildren (g : Goal) : Bool := g.children.isEmpty
@[inline] def mvar (g : Goal) : MVarId := g.preNormGoal

@[inline] def setId (id : GoalId) (g : Goal) : Goal := g.modify fun g => { g with id }
@[inline] def setParent (parent : PlatRef) (g : Goal) : Goal :=
  g.modify fun g => { g with parent }
@[inline] def setChildren (children : Array RappRef) (g : Goal) : Goal :=
  g.modify fun g => { g with children }
@[inline] def setDepth (depth : Nat) (g : Goal) : Goal := g.modify fun g => { g with depth }
@[inline] def setSlot (slot : GoalSlot) (g : Goal) : Goal := g.modify fun g => { g with slot }
@[inline] def setPre? (pre? : Option BubbleId) (g : Goal) : Goal :=
  g.modify fun g => { g with pre? }
@[inline] def setIsForcedUnprovable (isForcedUnprovable : Bool) (g : Goal) : Goal :=
  g.modify fun g => { g with isForcedUnprovable }
@[inline] def setPreNormGoal (preNormGoal : MVarId) (g : Goal) : Goal :=
  g.modify fun g => { g with preNormGoal }
@[inline] def setPreNormState (preNormState : SavedState) (g : Goal) : Goal :=
  g.modify fun g => { g with preNormState }
@[inline] def setNormalizationState
    (normalizationState : NormalizationState) (g : Goal) : Goal :=
  g.modify fun g => { g with normalizationState }
@[inline] def setUnassignedMvars (unassignedMvars : HashSet MVarId) (g : Goal) : Goal :=
  g.modify fun g => { g with unassignedMvars }
@[inline] def setSuccessProbability (successProbability : Percent) (g : Goal) : Goal :=
  g.modify fun g => { g with successProbability }
@[inline] def setAddedInIteration (addedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify fun g => { g with addedInIteration }
@[inline] def setLastExpandedInIteration
    (lastExpandedInIteration : Iteration) (g : Goal) : Goal :=
  g.modify fun g => { g with lastExpandedInIteration }
@[inline] def setRulesQueue? (rulesQueue? : Option RuleQueue) (g : Goal) : Goal :=
  g.modify fun g => { g with rulesQueue? }
@[inline] def setAppendiedGoalId (appendiedGoalId : Array GoalId) (g : Goal) : Goal :=
  g.modify fun g => { g with appendiedGoalId }
@[inline] def setMVar (mvar : MVarId) (g : Goal) : Goal := g.setPreNormGoal mvar

instance : BEq Goal where
  beq g₁ g₂ := g₁.id == g₂.id

instance : Hashable Goal where
  hash g := hash g.id

protected def isNormalized (g : Goal) : BaseIO Bool :=
  return g.normalizationState.isNormal

end Goal

namespace Rapp

@[inline]
protected def mk : RappData GoalRef PlatRef → Rapp :=
  tree.introRapp

instance : Nonempty Rapp :=
  ⟨Rapp.mk Classical.ofNonempty⟩

@[inline]
protected def elim : Rapp → RappData GoalRef PlatRef :=
  tree.elimRapp

@[inline]
protected def modify
    (f : RappData GoalRef PlatRef → RappData GoalRef PlatRef)
    (r : Rapp) : Rapp :=
  Rapp.mk <| f r.elim

@[inline] def id (r : Rapp) : RappId := r.elim.id
@[inline] def parent (r : Rapp) : GoalRef := r.elim.parent
@[inline] def children (r : Rapp) : PlatRef := r.elim.children
@[inline] def appliedRule (r : Rapp) : Rule RuleInfo := r.elim.appliedRule
@[inline] def usedHyps (r : Rapp) : Array AppliedHyp := r.elim.usedHyps
@[inline] def usedHyp? (r : Rapp) : Option AppliedHyp := r.usedHyps[0]?
@[inline] def consumedSpatialHyps (r : Rapp) : Array IrisHyp :=
  r.usedHyps.filterMap AppliedHyp.consumedSpatialHyp?
@[inline] def generatedSpatialHyps (r : Rapp) : Array IrisHyp := r.elim.generatedSpatialHyps
@[inline] def metaState (r : Rapp) : SavedState := r.elim.metaState
@[inline] def introducedMVars (r : Rapp) : HashSet MVarId := r.elim.introducedMVars
@[inline] def assignedMVars (r : Rapp) : HashSet MVarId := r.elim.assignedMVars

@[inline] def setId (id : RappId) (r : Rapp) : Rapp := r.modify fun r => { r with id }
@[inline] def setParent (parent : GoalRef) (r : Rapp) : Rapp :=
  r.modify fun r => { r with parent }
@[inline] def setChildren (children : PlatRef) (r : Rapp) : Rapp :=
  r.modify fun r => { r with children }
@[inline] def setAppliedRule (appliedRule : Rule RuleInfo) (r : Rapp) : Rapp :=
  r.modify fun r => { r with appliedRule }
@[inline] def setUsedHyps (usedHyps : Array AppliedHyp) (r : Rapp) : Rapp :=
  r.modify fun r => { r with usedHyps }
@[inline] def setGeneratedSpatialHyps
    (generatedSpatialHyps : Array IrisHyp) (r : Rapp) : Rapp :=
  r.modify fun r => { r with generatedSpatialHyps }
@[inline] def setMetaState (metaState : SavedState) (r : Rapp) : Rapp :=
  r.modify fun r => { r with metaState }
@[inline] def setIntroducedMVars (introducedMVars : HashSet MVarId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with introducedMVars }
@[inline] def setAssignedMVars (assignedMVars : HashSet MVarId) (r : Rapp) : Rapp :=
  r.modify fun r => { r with assignedMVars }

instance : BEq Rapp where
  beq r₁ r₂ := r₁.id == r₂.id

instance : Hashable Rapp where
  hash r := hash r.id

end Rapp

end Bubble
