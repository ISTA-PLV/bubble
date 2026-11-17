-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean.Util.Profile
public meta import Bubble.Index.Query
public meta import Bubble.Replay.Main
public meta import Bubble.Rule.Index
public meta import Bubble.Rule.Main
public meta import Bubble.Search.Commit
public meta import Bubble.Search.Propagation

public meta section

namespace Bubble.Search

open Lean Meta Std Elab Lean.Elab.Tactic

initialize registerTraceClass `ibubble.search

variable {Q : Type} [Queue Q]

/-- Check whether a goal can still be expanded by the search. -/
private def isGoalActive (goal : Goal) : Bool :=
  !goal.isForcedUnprovable &&
  !goal.normalizationState.isProvenByNorm &&
  match goal.rulesQueue? with
  | none => true
  | some queue => !queue.isEmpty

/-- Pop goals until an active goal is found or the search queue is empty. -/
private partial def nextActiveGoal? : SearchM Q (Option GoalRef) := do
  let some goalRef ← SearchM.popGoal? | return none
  let goal ← goalRef.get
  if isGoalActive goal then
    return some goalRef
  nextActiveGoal?

/-- Count uses of a theorem declaration on the direct ancestor path of a goal.
All orientations of the same declaration share one budget. -/
private partial def theoremUsesOnPath (goalRef : GoalRef) (decl : Name) : SearchM Q Nat := do
  let goal ← goalRef.get
  let platform ← goal.parent.get
  let some parentRappRef := platform.parent? | return 0
  let parentRapp ← parentRappRef.get
  let parentRule := parentRapp.appliedRule
  let usedHere := match parentRule.id.builder with
    | .backward _ | .forward _ => if parentRule.id.name == decl then 1 else 0
    | .tactic _ => 0
  return usedHere + (← theoremUsesOnPath parentRapp.parent decl)

/-- Run one matched rule, commit its outputs, and emit bubbles for closed Rapps. -/
private def runRule (goalRef : GoalRef) (matchResult : RuleMatch) :
    SearchM Q RuleCommitResult := do
  let config ← SearchM.getConfig
  trace[ibubble.search] "goal {(← goalRef.get).id} trying rule {matchResult.rule.id}"
  let theoremUses? ← match matchResult.rule.id.builder with
  | .backward _ | .forward _ =>
      let uses ← theoremUsesOnPath goalRef matchResult.rule.id.name
      if uses >= config.maxTheoremUses then
        trace[ibubble.search]
          m!"skipping theorem {matchResult.rule.id.name}: already used {uses} time(s)" ++
          m!" on this branch (limit {config.maxTheoremUses})"
        return .failed
      pure (some uses)
  | .tactic _ => pure none
  let some input ← mkRuleInput config goalRef matchResult
    | return .failed
  input.state.restore
  let output ← input.goal.withContext <| matchResult.rule.id.builder.run input
  if output.rappSpecs.isEmpty then
    trace[ibubble.search] "rule {matchResult.rule.id} did not apply to goal {(← goalRef.get).id}"
  else
    trace[ibubble.search] m!"rule {matchResult.rule.id} produced {output.rappSpecs.size}" ++
      m!" application candidate(s) for goal {(← goalRef.get).id}"
  let usedRule := match theoremUses? with
    | some uses =>
      /- Multiple use theorem should be given penalty. -/
        let penalty := Percent.medium ^ uses
        { matchResult.rule with successProb := matchResult.rule.successProb * penalty }
    | none => matchResult.rule
  if !output.rappSpecs.isEmpty && theoremUses?.getD 0 > 0 then
    trace[ibubble.search] m!"penalized theorem {matchResult.rule.id.name}: {theoremUses?.getD 0}" ++
      m!" previous use(s), effective probability {usedRule.successProb}"
  let result ← commitRuleOutput goalRef usedRule output
  match result with
  | .applied closedRapps => closedRapps.forM emitRappBubble
  | .failed => pure ()
  return result

/-- Return cached rule candidates or query the index for the normalized goal. -/
private def getRuleCandidates (parentRef : GoalRef) : SearchM Q RuleQueue := do
  let parent ← parentRef.get
  match parent.rulesQueue? with
  | some queue => return queue
  | none =>
      let index ← SearchM.getRuleIndex
      let goal := parent.normalizationState.normalizedGoal?.getD parent.preNormGoal
      let state := match parent.normalizationState with
        | .notNormal => parent.preNormState
        | .normal _ postState .. => postState
        | .provenByNorm postState .. => postState
      let previousState ← liftM (m := MetaM) saveState
      state.restore
      let results ← Index.queryMVar index goal
      previousState.restore
      return RuleQueue.ofArray results

/-- Skip failed candidates and apply the next rule that produces an expansion. -/
private partial def runNextApplicableRule (goalRef : GoalRef) :
    SearchM Q Unit := do
  let candidates ← getRuleCandidates goalRef
  let remaining ← pickLoop candidates
  goalRef.modify λ goal => goal.setRulesQueue? (some remaining)
where
  /-- Traverse the candidate queue until one rule applies or the queue is exhausted. -/
  pickLoop (queue : RuleQueue) : SearchM Q RuleQueue := do
    let some (matchResult, remaining) := queue.pop? | return queue
    match ← runRule goalRef matchResult with
    | .failed => pickLoop remaining
    | .applied _ => return remaining

/-- Find the next active goal and perform one expansion step. -/
private def expandNextGoal : SearchM Q Bool := do
  let some goalRef ← nextActiveGoal? | return false
  trace[ibubble.search] "selected goal {(← goalRef.get).id} for expansion"
  /- Normalization is always performed first. -/
  unless (← goalRef.get).normalizationState.isNormal do
    let config ← SearchM.getConfig
    let _ ← normalizeGoal config goalRef

  /- Read the goal again because normalization may have changed its state. -/
  let goal ← goalRef.get
  if goal.normalizationState.isProvenByNorm then
    emitNormalizationBubble goalRef
  else
    runNextApplicableRule goalRef

  /- If some remaining rules, add into goal queue. -/
  let iteration ← SearchM.getIteration
  goalRef.modify λ goal => goal.setLastExpandedInIteration iteration
  let goal ← goalRef.get
  if isGoalActive goal then SearchM.enqueueGoals #[goalRef]
  return true

/-- Run the search until a root bubble is found or no active goals remain. -/
private partial def searchLoop : SearchM Q (Array MVarId) := do
  checkSystem "ibubble"
  if let some rootBubble ← TreeM.getResult? then
    let config ← SearchM.getConfig
    return ← Replay.replayProof config rootBubble
  if ← expandNextGoal then
    SearchM.incrementIteration
    searchLoop
  else
    /- [TODO]: Instead of discarding all speculative steps and returning to the
      normalized root state, is there anything else we can do? -/
    let root ← (← TreeM.getRootGoal).get
    let (rootState, remaining) ← match root.normalizationState with
      | .notNormal => pure (root.preNormState, #[root.preNormGoal])
      | .normal postGoal postState .. => pure (postState, #[postGoal])
      | .provenByNorm .. => throwError
        "ibubble: search invariant violated: normalization closed the root goal, but no root bubble was emitted"
    rootState.restore
    return remaining

/-- Main entry for the search stage. -/
meta def search (goal : MVarId) (config : SearchConfig := {}) : TacticM (Array MVarId) := do
  goal.checkNotAssigned `ibubble
  let config := {
    config with maxNormIterations := max config.maxNormIterations config.maxDepth
  }
  let ruleIndex ← buildIndex config
  /- Pickup the specified strategy according to the configuration. -/
  Queue.withStrategy config.strategy λ Q => do
    let (remaining, _, _) ←
      SearchM.run (Q := Q) config ruleIndex goal searchLoop
    return remaining

end Bubble.Search
