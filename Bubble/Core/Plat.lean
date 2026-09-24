-- SPDX-License-Identifier: Apache-2.0
 module

public meta import Bubble.Core.TreeM

public meta section

namespace Bubble.Plat

open Lean Lean.Meta Std
open Iris.ProofMode

structure ReconstructedPath where
  root     : Group
  prefixes : Array (GoalSlot × BubbleId)
  consumed : Array IrisHyp
  metaInfo : Array MetaAssignment

/--
  Follow a residual-group chain and reconstruct all context carried by its
  prefix bubbles together with the arriving bubble.
-/
partial def reconstructPath (plat : Plat) (group : Group) (arriving : Bubble) :
    TreeM (Option ReconstructedPath) := do
  let some rappRef := plat.parent? | return none
  let rapp ← rappRef.get
  let (root, prefixes) ← collectPrefixes plat group
  let bubbles := (prefixes.map (·.2)).push arriving.id
  let mut consumed : Array IrisHyp := #[]
  let mut parts : Array (Array MetaAssignment) := #[]
  for bubbleId in bubbles do
    let some bubble ← TreeM.getBubble? bubbleId
      | throwError "ibubble (plat): unknown bubble {bubbleId}"
    let some next := Join.appendResources plat.kind consumed bubble.consumed
      | throwError "ibubble (plat): residual path for group {group.id} reuses a spatial resource at bubble {bubbleId}"
    consumed := next
    parts := parts.push bubble.metaInfo
  let some metaInfo ← Bubble.Meta.mergeMetaInfo rapp.metaState parts
    | throwError "ibubble (plat): residual path for group {group.id} contains incompatible metavariable assignments"
  return some { root, prefixes, consumed, metaInfo }
where
  collectPrefixes (plat : Plat) (group : Group) :
      TreeM (Group × Array (GoalSlot × BubbleId)) := do
    match group.link? with
    | none => return (group, #[])
    | some link =>
        let some predecessor := plat.groups.find? λ candidate =>
            candidate.id == link.predecessor
          | throwError
              "ibubble (plat): predecessor group {link.predecessor} is missing"
        let (root, prefixes) ← collectPrefixes plat predecessor
        return (root, prefixes.push (link.slot, link.bubble))

/--
  Apply an arriving bubble to every remaining member and create the next
  residual group. Linear platforms additionally remove its footprint.
-/
private def spawnResidual (iteration : Iteration) (platRef : PlatRef) (group : Group)
    (sourceRef : GoalRef) (bubble : Bubble) : TreeM (Option (Array GoalRef)) := do
  let plat ← platRef.get
  let some { consumed, metaInfo, .. } ← reconstructPath plat group bubble | return none
  let source ← sourceRef.get
  let mut residualGoals : Array GoalRef := #[]
  for siblingId in group.goals do
    if siblingId == source.id then continue

    /- Find sibling's original goalRef and refine it with collected metaInfo. -/
    let some originalRef ← plat.goals.findM? λ goalRef => do
        return (← goalRef.get).id == siblingId
      | throwError "ibubble (plat): platform {plat.id} does not own goal {siblingId}"
    let original ← originalRef.get
    let some refinedState ← Bubble.Meta.applyMetaInfo original.preNormState metaInfo
      | throwError "ibubble (plat): failed to refine goal {original.id} with bubble {bubble.id}"

    /- Remove used hypotheses from iris context. -/
    let (goalMVar, postState, dependencies) ← refinedState.runMetaM' do
      original.preNormGoal.withContext do
        let type ← instantiateMVars (← original.preNormGoal.getType)
        let some template := parseIrisGoal? type
          | throwError "ibubble (plat): residual group expected an Iris goal"
        let template ← if plat.kind.isLinear then
          consumed.foldlM (init := template) λ goal used => do
            if !goal.hyps.spatialIVarIds.contains used.ivar then return goal
            let ⟨e, hyps, _, _, _, _, _⟩ := goal.hyps.remove false used.ivar
            return { goal with e, hyps }
          else pure template
        let type ← instantiateMVars template.toExpr
        let goalMVar := (← mkFreshExprSyntheticOpaqueMVar type (← original.preNormGoal.getTag)).mvarId!
        return (goalMVar, ← saveState, ← goalMVar.getMVarDependencies)

    /- Creat new goal's node and add into current plat node. -/
    let residualRef ← IO.mkRef <| Goal.mk {
      id := ← TreeM.getAndIncrementNextGoalId
      parent := platRef
      children := #[]
      depth := original.depth
      slot := original.slot
      pre? := some bubble.id
      isForcedUnprovable := original.isForcedUnprovable
      preNormGoal := goalMVar
      preNormState := postState
      normalizationState := .notNormal
      unassignedMvars := dependencies
      successProbability := original.successProbability
      addedInIteration := iteration
      lastExpandedInIteration := iteration
      rulesQueue? := none
      appendiedGoalId := #[]
    }
    TreeM.addGoal residualRef
    residualGoals := residualGoals.push residualRef

  /- Create new residual group mentioning the new residual goals. -/
  if residualGoals.isEmpty then
    throwError "ibubble (plat): bubble {bubble.id} left no goals in group {group.id}"
  let residual : Group := {
    id := ← TreeM.getAndIncrementNextGroupId
    goals := ← residualGoals.mapM λ goalRef => return (← goalRef.get).id
    link? := some {
      predecessor := group.id
      slot := source.slot
      bubble := bubble.id
    }
  }
  trace[ibubble.search]
    "created residual group {residual.id} from group {group.id} using bubble {bubble.id}; goals {residual.goals}"
  for residualRef in residualGoals do
    let residualGoal ← residualRef.get
    let rendered ← residualGoal.preNormState.runMetaM' do
      ppGoal residualGoal.preNormGoal
    trace[ibubble.search]
      m!"residual goal {residualGoal.id} | slot {residualGoal.slot}" ++
      m!" | dependencies {residualGoal.unassignedMvars.size}\n{rendered}"
  platRef.modify λ current => (current.setGoals (current.goals ++ residualGoals))
    |>.setGroups (current.groups.push residual)
  return some residualGoals

/--
  Entry point for bubble and platform interaction.
-/
def arriveBubble (iteration : Iteration) (goalRef : GoalRef) (bubble : Bubble) :
    TreeM (Array JoinEmission × Array GoalRef) := do
  let goal ← goalRef.get
  let platRef := goal.parent
  let plat ← platRef.get
  if plat.kind.isSingle then
    throwError "ibubble (plat): a bubble must not arrive at a single-goal platform"

  /- Locate the group currently containing the solved goal. -/
  let some group := plat.groups.find? λ group => group.goals.contains goal.id
    | throwError "ibubble (plat): goal {goal.id} does not belong to a group in platform {plat.id}"
  trace[ibubble.search]
    "platform {plat.id} found group {group.id} with {group.goals.size} goal(s)"
  if group.goals.size > 1 then
    trace[ibubble.search] "platform {plat.id} spawning a residual group"
    let some residualGoals ← spawnResidual iteration platRef group goalRef bubble
      | throwError "ibubble (plat): bubble {bubble.id} failed to trigger residual group generation"
    return (#[], residualGoals)
  if group.goals.isEmpty then
    throwError "ibubble (plat): bubble {bubble.id} arrived at empty group {group.id}"

  /- The arriving bubble closes the final member of this group chain. -/
  trace[ibubble.search] "platform {plat.id} reconstructing a completed group path"
  let some path ← reconstructPath plat group bubble | return (#[], #[])
  if path.prefixes.size + 1 != path.root.goals.size then
    throwError "ibubble (plat): expected {path.root.goals.size} bubbles, found {path.prefixes.size + 1}"
  let candidate : JoinCandidate := {
    bubble := bubble.id
    consumed := path.consumed
    metaInfo := path.metaInfo
  }
  let current ← platRef.get
  let some rappRef := current.parent?
    | throwError "ibubble (plat): non-root platform {current.id} has no parent Rapp"
  let rapp ← rappRef.get
  trace[ibubble.search] "platform {plat.id} registering a join candidate"
  let (join, emissions) ← current.join.registerCandidate
    current.kind rapp.metaState path.root.id candidate
  platRef.modify λ latest =>
    (latest.setBubbleToGroup <| latest.bubbleToGroup.insert bubble.id group.id)
      |>.setJoin join
  return (emissions, #[])

end Bubble.Plat
