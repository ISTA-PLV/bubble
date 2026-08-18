module

public meta import Bubble.Replay.Basic
public meta import Bubble.Replay.ReplayM
public meta import Bubble.Search.Normalization

public meta section

namespace Bubble.Replay

open Lean Lean.Meta Lean.Elab.Tactic

/-- Run normalization and record its successful tactic steps for replay when requested. -/
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

/-- Replay normalization on the current goal and record its successful steps. -/
def normalize (focus : MVarId) (goal : Goal) :
    ReplayM (Search.NormSeqResult × Array MVarId) := do
  let config ← ReplayM.getConfig
  let (result, script, remaining) ←
    normalizeGoalMVar focus goal.depth config.maxNormIterations
      config.enableSimp? goal.unassignedMvars config.generateScript?
  ReplayM.appendScript script
  return (result, ← ReplayM.openGoals remaining)

/-- Normalize a goal before replaying its selected rule application. -/
def normalizeForRuleApplication (focus : MVarId) (goal : Goal) :
    ReplayM (MVarId × Array MVarId) := do
  let (result, remaining) ← normalize focus goal
  let normalizedFocus ← match result with
    | .proved => throwError
        "ibubble: normalization unexpectedly closed a rule goal during replay"
    | .changed goal => pure goal
    | .unchanged => pure focus
  return (normalizedFocus, remaining)

end Bubble.Replay
