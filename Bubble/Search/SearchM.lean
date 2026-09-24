-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.TreeM
public meta import Bubble.Index.Basic
public meta import Bubble.Search.Queue

public meta section

namespace Bubble.Search

open Lean Meta

namespace SearchM

structure Context where
  config : SearchConfig
  ruleIndex : Index RuleInfo

structure State (Q : Type) where
  iteration : Iteration := 1
  queue : Q
  maxDepthReached : Bool := false

end SearchM

abbrev SearchM (Q : Type) [Queue Q] :=
  ReaderT SearchM.Context <| StateRefT (SearchM.State Q) TreeM

namespace SearchM

variable {Q : Type} [Queue Q]

def run (config : SearchConfig) (ruleIndex : Index RuleInfo)
    (goal : MVarId) (action : SearchM Q α) :
    Lean.Elab.Tactic.TacticM (α × State Q × SearchStore) := do
  let store ← mkInitialStore goal
  let initialGoals := (← store.root.get).goals
  let state : State Q := { queue := ← Queue.ofArray initialGoals }
  let ((result, state), store) ←
    TreeM.run {} store <| (ReaderT.run action { config, ruleIndex }).run state
  return (result, state, store)

def getConfig : SearchM Q SearchConfig :=
  return (← readThe Context).config

def getRuleIndex : SearchM Q (Index RuleInfo) :=
  return (← readThe Context).ruleIndex

def getIteration : SearchM Q Iteration :=
  return (← getThe (State Q)).iteration

def incrementIteration : SearchM Q Unit :=
  modifyThe (State Q) fun state => { state with iteration := state.iteration + 1 }

def popGoal? : SearchM Q (Option GoalRef) := do
  let state ← getThe (State Q)
  let (goal?, queue) ← Queue.pop? state.queue
  set { state with queue }
  return goal?

def enqueueGoals (goals : Array GoalRef) : SearchM Q Unit := do
  let state ← getThe (State Q)
  let queue ← Queue.insert state.queue goals
  set { state with queue }

def setMaxDepthReached : SearchM Q Unit :=
  modifyThe (State Q) fun state => { state with maxDepthReached := true }

end SearchM

end Bubble.Search
