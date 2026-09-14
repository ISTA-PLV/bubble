module

public meta import Bubble.Core.Bubble
public meta import Bubble.Core.Group
public meta import Bubble.Core.Join
public meta import Bubble.Frontend.Main
public meta import Bubble.Index.Query
public meta import Bubble.Search.Main

public meta section

namespace Bubble

open Lean Elab Tactic Iris

register_option ibubble.timing : Bool := {
  defValue := false
  descr := "report the time spent in Bubble search and proof replay"
}

@[tactic ibubbleTactic, tactic ibubbleTactic?]
meta def evalIBubble : Tactic := λ stx => do
  withRef stx do
    let config ← parse stx
    let (subgoal, _) ← ProofMode.startProofMode (← getMainGoal)
    subgoal.withContext do
      let timingEnabled := ibubble.timing.get (← getOptions)
      let started ← if timingEnabled then IO.monoNanosNow else pure 0
      let remaining ← Search.search subgoal config
      if timingEnabled then
        let elapsed := (← IO.monoNanosNow) - started
        logInfoAt stx m!"IBUBBLE_CORE_TIME_NS {elapsed}"
      -- Make sure to synthesize everything postponed
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)

      -- Put the goals that depend on other goals last
      let dependees ← remaining.foldlM (init := ∅) λ m g => do
        return m ∪ (← g.getMVarDependencies)
      let (dependent, independent) := remaining.partition dependees.contains
      replaceMainGoal (independent ++ dependent).toList

end Bubble
