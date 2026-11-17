-- SPDX-License-Identifier: Apache-2.0
module

public meta import Qq
public meta import Iris.ProofMode.Tactics
public meta import Bubble.Rule.Runner
public meta import Bubble.Search.Names

public meta section

namespace Bubble.Tactic

open Lean Elab Lean.Elab.Tactic Meta Qq Std
open Iris.ProofMode

initialize registerTraceClass `ibubble.rule

def irisGoal? (goal : MVarId) : MetaM (Option IrisGoal) :=
  goal.withContext do
    return parseIrisGoal? (← instantiateMVars (← goal.getType))

/- Treat typeclass-search exceptions as failed speculative probes and restore the metavariable state. -/
def trySynthInstanceProbeQ {u : Level} (type : Q(Sort u)) :
    MetaM (LOption (Q($type) × Std.HashSet MVarId)) := do
  let preState ← saveState
  try
    Iris.ProofMode.trySynthInstance type
  catch _ =>
    preState.restore
    return .none

/- Record spatial hypotheses removed, introduced, or changed by a tactic. -/
def spatialDiff (pre post : IrisGoal) : MetaM (Array IrisHyp × Array IrisHyp) := do
  let preHyps := Bubble.Search.spatialHypEntries pre.hyps
  let postHyps := Bubble.Search.spatialHypEntries post.hyps
  let mut consumed := #[]
  let mut generated := #[]
  for (preName, preIVar, preType) in preHyps do
    match postHyps.find? (·.2.1 == preIVar) with
    | none => consumed := consumed.push { name := preName, ivar := preIVar }
    | some (postName, postIVar, postType) =>
        unless ← isDefEq preType postType do
          consumed := consumed.push { name := preName, ivar := preIVar }
          generated := generated.push { name := postName, ivar := postIVar }
  for (postName, postIVar, _) in postHyps do
    if preHyps.all (·.2.1 != postIVar) then
      generated := generated.push { name := postName, ivar := postIVar }
  return (consumed, generated)

end Bubble.Tactic
