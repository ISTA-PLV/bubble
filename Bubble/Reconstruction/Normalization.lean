-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Reconstruction.Basic
public meta import Bubble.Reconstruction.ReconM
public meta import Bubble.Search.Normalization

public meta section

namespace Bubble.Reconstruction

open Lean Lean.Meta Lean.Elab.Tactic

/-- Run normalization and record its successful tactic steps for reconstruction when requested. -/
def normalizeGoalMVar (goal : MVarId) (depth maxIterations : Nat)
    (enableSimp : Bool) (goalMVars : Std.HashSet MVarId)
    (recordScript : Bool) : TacticM (Search.NormSeqResult × UScript × Array MVarId) := do
  let scriptRef ← IO.mkRef (#[] : UScript)
  let observer? : Option Search.NormStepObserver ←
    if recordScript then
      pure <| some λ preState preGoal tactic postState postGoals =>
        scriptRef.modify λ script =>
          script.push { preState, preGoal, tactic, postState, postGoals }
    else
      pure none
  let (result, remaining) ← Search.normalizeGoalMVar goal depth maxIterations
    enableSimp goalMVars observer?
  return (result, ← scriptRef.get, remaining)

/-- Normalize the current goal and record its successful reconstruction steps. -/
def normalize (focus : MVarId) (goal : Goal) :
    ReconM (Search.NormSeqResult × Array MVarId) := do
  let config ← ReconM.getConfig
  let (result, script, remaining) ←
    normalizeGoalMVar focus goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars config.generateScript?
  ReconM.appendScript script
  return (result, ← ReconM.openGoals remaining)

/-- Normalize a goal before reconstructing its selected rule application. -/
def normalizeForRuleApplication (focus : MVarId) (goal : Goal) :
    ReconM (MVarId × Array MVarId) := do
  if let .normal postGoal _ _ _ := goal.normalizationState then
    if postGoal == goal.preNormGoal then
      return (focus, #[])
  let (result, remaining) ← normalize focus goal
  let normalizedFocus ← match result with
    | .proved => throwError
        "ibubble: normalization unexpectedly closed a rule goal during reconstruction"
    | .changed goal => pure goal
    | .unchanged => pure focus
  return (normalizedFocus, remaining)

end Bubble.Reconstruction
