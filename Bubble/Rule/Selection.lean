module

public meta import Bubble.Index.Query
public meta import Bubble.Search.SearchM

public meta section

namespace Bubble.Rule

open Lean Meta
open Bubble.Search

variable {Q : Type} [Queue Q]

/-- Return cached rule candidates or query the index for the normalized goal. -/
def select (parentRef : GoalRef) : SearchM Q RuleQueue := do
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

end Bubble.Rule
