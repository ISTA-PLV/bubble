-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean.Meta.Basic
public import Iris.ProofMode.Expr
public meta import Bubble.Rule.Types

public meta section

open Lean Meta Iris.ProofMode

namespace Bubble

-- Only record the spatial iris-hypothesis
structure IrisHyp where
  name : Name
  ivar : IVarId
  deriving Inhabited, BEq, Hashable

namespace IrisHyp

instance : ToString IrisHyp where
  toString := (·.name.toString)

end IrisHyp

/- Record the concrete hypothesis used by a rule application. -/
inductive AppliedHyp where
  | spatial (hyp : IrisHyp)
  | intuitionistic (hyp : IrisHyp)
  | lean (userName : Name) (fvarId : FVarId)

namespace AppliedHyp

instance : ToString AppliedHyp where
  toString
    | spatial hyp => s!"spatial {hyp}"
    | intuitionistic hyp => s!"intuitionistic {hyp}"
    | lean userName _ => s!"lean {userName}"

def consumedSpatialHyp? : AppliedHyp → Option IrisHyp
  | .spatial hyp => some hyp
  | _ => none

end AppliedHyp

abbrev Iteration := Nat

abbrev GoalSlot := Nat

/- A metavariable assignment carried by a proof bubble. -/
structure MetaAssignment where
  mvarId : MVarId
  value : Expr
  sourceState : Meta.SavedState

inductive NodeKind
  | goal
  | rapp
  | plat
  | bubble
  | group
  deriving Repr, DecidableEq

structure NodeId (kind : NodeKind) where
  toNat : Nat
  deriving Inhabited, DecidableEq, BEq, Hashable, Repr, Ord

namespace NodeId

protected def zero : NodeId kind :=
  ⟨0⟩

protected def one : NodeId kind :=
  ⟨1⟩

protected def succ : NodeId kind → NodeId kind
  | ⟨n⟩ => ⟨n + 1⟩

instance : ToString (NodeId kind) where
  toString id := toString id.toNat

end NodeId

abbrev GoalId   := NodeId .goal
abbrev RappId   := NodeId .rapp
abbrev PlatId   := NodeId .plat
abbrev BubbleId := NodeId .bubble
abbrev GroupId  := NodeId .group

inductive PlatKind
  | single
  | ordinary
  | linear
  deriving Repr, Inhabited, BEq

namespace PlatKind

instance : ToString PlatKind where
  toString
    | .single => "single"
    | .ordinary => "ordinary"
    | .linear => "linear"

def isSingle : PlatKind → Bool
  | .single => true
  | _ => false

def isOrdinary : PlatKind → Bool
  | .ordinary => true
  | _ => false

def isLinear : PlatKind → Bool
  | .linear => true
  | _ => false

end PlatKind

inductive NormalizationState
  | notNormal
  | normal (postGoal : MVarId) (postState : Meta.SavedState)
      (generatedSpatialHyps : Array IrisHyp) (usedSpatialHyps : Array IrisHyp)
  | provenByNorm (postState : Meta.SavedState)
      (generatedSpatialHyps : Array IrisHyp) (usedSpatialHyps : Array IrisHyp)
  deriving Inhabited

namespace NormalizationState

def isNormal : NormalizationState → Bool
  | notNormal => false
  | normal .. => true
  | provenByNorm .. => true

def isProvenByNorm : NormalizationState → Bool
  | notNormal .. => false
  | normal .. => false
  | provenByNorm .. => true

def normalizedGoal? : NormalizationState → Option MVarId
  | notNormal .. | provenByNorm .. => none
  | normal (postGoal := g) .. => g

def generatedSpatialHyps : NormalizationState → Array IrisHyp
  | notNormal => #[]
  | normal (generatedSpatialHyps := hyps) .. => hyps
  | provenByNorm (generatedSpatialHyps := hyps) .. => hyps

def usedSpatialHyps : NormalizationState → Array IrisHyp
  | notNormal => #[]
  | normal (usedSpatialHyps := hyps) .. => hyps
  | provenByNorm (usedSpatialHyps := hyps) .. => hyps

end NormalizationState

end Bubble
