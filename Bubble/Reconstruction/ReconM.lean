-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.TreeM
public meta import Bubble.Reconstruction.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble.Reconstruction

open Lean Lean.Elab.Tactic Lean.Meta

initialize registerTraceClass `ibubble.reconstruction

namespace ReconM

structure Context where
  config : SearchConfig

structure State where
  script : UScript := #[]

end ReconM

abbrev ReconM :=
  ReaderT ReconM.Context <| StateRefT ReconM.State TreeM

namespace ReconM

/-- Return the search configuration used by reconstruction. -/
def getConfig : ReconM SearchConfig :=
  return (← readThe Context).config

/-- Retrieve a bubble referenced by the reconstruction certificate. -/
def getBubble (id : BubbleId) : ReconM Bubble := do
  let some bubble ← TreeM.getBubble? id
    | throwError "ibubble: reconstruction references unknown bubble {id}"
  return bubble

/-- Retrieve a goal referenced by the reconstruction certificate. -/
def getGoal (id : GoalId) : ReconM GoalRef := do
  let some goal ← TreeM.getGoal? id
    | throwError "ibubble: reconstruction references unknown goal {id}"
  return goal

/-- Retrieve a rule application referenced by the reconstruction certificate. -/
def getRapp (id : RappId) : ReconM RappRef := do
  let some rapp ← TreeM.getRapp? id
    | throwError "ibubble: reconstruction references unknown Rapp {id}"
  return rapp

/-- Append successful tactic steps to the generated reconstruction script. -/
def appendScript (steps : UScript) : ReconM Unit :=
  unless steps.isEmpty do
    modifyThe State λ state => { state with script := state.script ++ steps }

/-- Retain only unresolved metavariable goals. -/
def openGoals (goals : Array MVarId) : ReconM (Array MVarId) := do
  goals.foldlM (init := #[]) fun result goal => do
    if ← goal.isAssignedOrDelayedAssigned then return result
    return result.push goal

end ReconM

end Bubble.Reconstruction
