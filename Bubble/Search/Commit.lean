-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Runner
public meta import Bubble.Search.SearchM

public meta section

namespace Bubble.Search

open Lean Meta Std

variable {Q : Type} [Queue Q]

inductive RuleCommitResult where
  | failed
  /- Only carry closed Rapps since they will trigger bubble emission. -/
  | applied (closedRapps : Array RappRef)

namespace Commit

/-- Platform kind is determined by RappSpec's `goals` size and `multiGoalAction?` -/
private def platformKind (spec : RappSpec) : SearchM Q PlatKind := do
  if spec.goals.size ≤ 1 then
    if spec.effect.multiGoalAction?.isSome then
      throwError "ibubble (commit): a Rapp with at most one child goal must not specify a multi-goal action"
    return .single
  else match spec.effect.multiGoalAction? with
    | some .shareContext => return .ordinary
    | some .partitionContext => return .linear
    | none => throwError "ibubble (commit): a Rapp with multiple child goals must specify a multi-goal action"

/-- Commit based on the RappSpec's content. -/
private def commitSpec (parentRef : GoalRef) (usedRule : Rule)
    (spec : RappSpec) : SearchM Q (RappRef × Array GoalRef) := do
  let parent ← parentRef.get
  let goalProbability := parent.successProbability * usedRule.successProb
  let kind ← platformKind spec
  /- Construct a platform containing its groups and child goals. -/
  let platformRef ← IO.mkRef <| Plat.mk {
    id := ← TreeM.getAndIncrementNextPlatId
    parent? := none
    goals := #[]
    groups := #[]
    join := { roots := #[] }
    kind
    bubbleToGroup := {}
  }

  /- Construct the child goal based on spec's content one by one. -/
  let iteration ← SearchM.getIteration
  let mut goalRefs : Array GoalRef := #[]
  let mut goalDependencies : Array (GoalId × HashSet MVarId) := #[]
  for slot in [:spec.goals.size] do
    let child := spec.goals[slot]!
    let id ← TreeM.getAndIncrementNextGoalId
    let goalRef ← IO.mkRef <| Goal.mk {
      id
      parent := platformRef
      children := #[]
      depth := parent.depth + 1
      slot
      isForcedUnprovable := parent.depth + 1 > (← SearchM.getConfig).maxDepth
      preNormGoal := child.goal
      preNormState := spec.postState
      normalizationState := .notNormal
      unassignedMvars := child.dependencies
      successProbability := goalProbability
      addedInIteration := iteration
      lastExpandedInIteration := iteration
      rulesQueue? := none
      appendiedGoalId := #[]
    }
    TreeM.addGoal goalRef
    goalRefs := goalRefs.push goalRef
    goalDependencies := goalDependencies.push (id, child.dependencies)
    let rendered ← spec.postState.runMetaM' <| ppGoal child.goal
    trace[ibubble.search] m!"created goal node {id} from rule {usedRule.id}" ++
      m!"\n  depth {parent.depth + 1} | slot {slot}" ++
      m!" | platform {(← platformRef.get).id} ({kind})" ++
      m!" | dependencies {child.dependencies.size}" ++
      m!"\n{rendered}"

  /- Construct the group based on child goal's metavariables info -/
  let mut groups : Array Group := #[]
  for component in Group.partitionDependencies goalDependencies do
    groups := groups.push {
      id := ← TreeM.getAndIncrementNextGroupId
      goals := component
      link? := none
    }

  /- Collect the metavariable changes recorded by the new Rapp node. -/
  let introducedMVars := goalDependencies.foldl (init := {}) λ introduced ⟨_, mvars⟩ =>
    mvars.fold (init := introduced) λ introduced mvar =>
      if parent.unassignedMvars.contains mvar then introduced
      else introduced.insert mvar
  let assignedMVars ← do
    spec.postState.restore
    parent.unassignedMvars.foldM (init := {}) λ assigned mvar => do
      return if ← mvar.isAssigned then assigned.insert mvar else assigned

  /- Construct the new Rapp node. -/
  let rappRef ← IO.mkRef <| Rapp.mk {
    id := ← TreeM.getAndIncrementNextRappId
    parent := parentRef
    children := platformRef
    appliedRule := usedRule
    usedHyps := spec.effect.usedHyps
    generatedSpatialHyps := spec.effect.generatedSpatialHyps
    metaState := spec.postState
    introducedMVars
    assignedMVars
  }
  TreeM.addRapp rappRef
  platformRef.modify λ platform =>
    (platform.setParent rappRef)
      |>.setGoals goalRefs
      |>.setGroups groups
      |>.setJoin { roots := groups.map (·.id) }
  unless goalRefs.isEmpty do
    SearchM.enqueueGoals goalRefs
  return (rappRef, goalRefs)

end Commit

/-- Commit a rule's output to the target goal node by creating child Rapp nodes. -/
def commitRuleOutput (goalRef : GoalRef) (usedRule : Rule)
    (output : RuleOutput) : SearchM Q RuleCommitResult := do
  if output.rappSpecs.isEmpty then return .failed
  /- Collect every Rapp for the goal and closed Rapps for bubble emission. -/
  let mut allRapps : Array RappRef := #[]
  let mut closedRapps : Array RappRef := #[]
  for spec in output.rappSpecs do
    let (rappRef, goals) ← Commit.commitSpec goalRef usedRule spec
    allRapps := allRapps.push rappRef
    if goals.isEmpty then closedRapps := closedRapps.push rappRef
  goalRef.modify λ goal =>
    goal.setChildren (goal.children ++ allRapps)
  return .applied closedRapps

end Bubble.Search
