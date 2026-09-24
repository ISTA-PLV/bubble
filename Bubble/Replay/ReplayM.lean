-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.TreeM
public meta import Bubble.Replay.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble.Replay

open Lean Lean.Elab.Tactic Lean.Meta

initialize registerTraceClass `ibubble.replay

namespace ReplayM

structure Context where
  config : SearchConfig

structure State where
  script : UScript := #[]

end ReplayM

abbrev ReplayM :=
  ReaderT ReplayM.Context <| StateRefT ReplayM.State TreeM

namespace ReplayM

/-- Return the search configuration used by replay. -/
def getConfig : ReplayM SearchConfig :=
  return (← readThe Context).config

/-- Retrieve a bubble referenced by the replay certificate. -/
def getBubble (id : BubbleId) : ReplayM Bubble := do
  let some bubble ← TreeM.getBubble? id
    | throwError "ibubble: replay references unknown bubble {id}"
  return bubble

/-- Retrieve a goal referenced by the replay certificate. -/
def getGoal (id : GoalId) : ReplayM GoalRef := do
  let some goal ← TreeM.getGoal? id
    | throwError "ibubble: replay references unknown goal {id}"
  return goal

/-- Retrieve a rule application referenced by the replay certificate. -/
def getRapp (id : RappId) : ReplayM RappRef := do
  let some rapp ← TreeM.getRapp? id
    | throwError "ibubble: replay references unknown Rapp {id}"
  return rapp

/-- Append successful tactic steps to the generated replay script. -/
def appendScript (steps : UScript) : ReplayM Unit :=
  unless steps.isEmpty do
    modifyThe State λ state => { state with script := state.script ++ steps }

/-- Retain only unresolved metavariable goals. -/
def openGoals (goals : Array MVarId) : ReplayM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

end ReplayM

end Bubble.Replay
