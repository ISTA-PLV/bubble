module

public meta import Iris.ProofMode

public meta section
namespace BubbleTest.Robustness
open Lean Elab Tactic

/-- Sidecar output is visible during elaboration, unlike captured tactic stdout. -/
def emitMeasurement (line : String) : TacticM Unit := do
  if let some path ← IO.getEnv "BUBBLE_ROBUSTNESS_MARKERS" then
    IO.FS.withFile path .append fun stream => do
      stream.putStrLn line
      stream.flush
  else
    logInfo m!"{line}"

/-- Same boundary for both tactics: preparation, search, replay and postponed
elaboration. The runner additionally requires successful declaration checking. -/
elab "robustness_timed " t:tactic : tactic => do
  emitMeasurement "ROBUSTNESS_START"
  let started ← IO.monoNanosNow
  let heartbeats ← IO.getNumHeartbeats
  evalTactic t
  Term.synthesizeSyntheticMVarsNoPostponing
  let elapsed := (← IO.monoNanosNow) - started
  let used := (← IO.getNumHeartbeats) - heartbeats
  emitMeasurement s!"ROBUSTNESS_END {elapsed} {used}"

end BubbleTest.Robustness
