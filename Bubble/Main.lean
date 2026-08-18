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

@[tactic ibubbleTactic, tactic ibubbleTactic?]
meta def evalIBubble : Tactic := λ stx => do
  withRef stx do
    let config ← parse stx
    let (subgoal, _) ← ProofMode.startProofMode (← getMainGoal)
    subgoal.withContext do
      let remaining ← Search.search subgoal config
      -- Make sure to synthesize everything postponed
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)

      -- Put the goals that depend on other goals last
      let dependees ← remaining.foldlM (init := ∅) λ m g => do
        return m ∪ (← g.getMVarDependencies)
      let (dependent, independent) := remaining.partition dependees.contains
      replaceMainGoal (independent ++ dependent).toList

end Bubble
