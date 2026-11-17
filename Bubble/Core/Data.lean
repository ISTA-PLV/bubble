-- SPDX-License-Identifier: Apache-2.0
module

public import Iris.ProofMode.Expr
public import Bubble.Core.Types
public import Bubble.Core.Bubble
public import Bubble.Core.Group
public import Bubble.Core.Join
public import Bubble.Util.Percent

public section

namespace Bubble

open Lean Lean.Meta Std

structure GoalData (RappRef PlatRef : Type) : Type where
  id : GoalId
  parent : PlatRef
  children : Array RappRef
  depth : Nat
  slot : GoalSlot
  /- Bubble that must be reconstructed before this residual goal. -/
  pre? : Option BubbleId := none

  -- Turn true because of reaching the search depth limit
  isForcedUnprovable : Bool
  preNormGoal : MVarId
  preNormState : SavedState
  normalizationState : NormalizationState

  unassignedMvars : Std.HashSet MVarId
  successProbability : Bubble.Percent
  addedInIteration : Iteration
  lastExpandedInIteration : Iteration

  /- `none` <=> not norm; `some queue` stores the untried rules, which may be empty. -/
  rulesQueue? : Option RuleQueue := none
  appendiedGoalId : Array GoalId
  deriving Nonempty

structure PlatData (GoalRef RappRef : Type) : Type where
  id : PlatId
  parent? : Option RappRef
  goals : Array GoalRef
  groups : Array Group
  join : Join
  kind : PlatKind

  /-- Maps each bubble ID to the ID of the group to which it belongs. -/
  bubbleToGroup : Std.HashMap BubbleId GroupId

  deriving Nonempty

structure RappData (GoalRef PlatRef : Type) : Type where
  id : RappId
  parent : GoalRef
  children : PlatRef

  appliedRule : Rule

  /- Spatial hypotheses generated/removed by this rule application. -/
  usedHyps : Array AppliedHyp
  generatedSpatialHyps : Array IrisHyp


  metaState : SavedState
  introducedMVars : Std.HashSet MVarId
  assignedMVars : Std.HashSet MVarId

  deriving Nonempty

end Bubble
