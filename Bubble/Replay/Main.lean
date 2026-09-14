module

public meta import Bubble.Core.Plat
public meta import Bubble.Replay.ReplayM
public meta import Bubble.Replay.Normalization
public meta import Bubble.Replay.RuleApplication

public meta section

namespace Bubble.Replay

open Lean Lean.Elab.Tactic Lean.Meta
open Iris.ProofMode
open ReplayM

private structure PlatformChild where
  slot   : GoalSlot
  bubble : BubbleId

/-- Expand one terminal bubble per completed root group into the complete child
bubble sequence required to replay the platform's Rapp. -/
private def expandPlatformChildren (plat : Plat) (terminals : Array BubbleId) :
    ReplayM (Array PlatformChild) := do
  let mut entries : Array PlatformChild := #[]
  for terminalId in terminals do
    let some groupId := plat.groupForBubble? terminalId
      | throwError "ibubble: replay cannot locate terminal bubble {terminalId} in platform {plat.id}"
    let some group := plat.groups.find? λ candidate => candidate.id == groupId
      | throwError "ibubble: replay cannot find terminal group {groupId}"
    let terminal ← getBubble terminalId
    let terminalGoal ← (← getGoal terminal.goal).get
    unless group.goals.contains terminalGoal.id do
      throwError "ibubble: terminal bubble {terminalId} does not belong to group {groupId}"
    let some path ← Plat.reconstructPath plat group terminal
      | throwError "ibubble: replay cannot reconstruct the path ending at bubble {terminalId}"
    entries := entries ++ path.prefixes.map λ entry =>
      { slot := entry.1, bubble := entry.2 }
    entries := entries.push { slot := terminalGoal.slot, bubble := terminalId }
  let mut slots : Std.HashSet GoalSlot := {}
  for entry in entries do
    if slots.contains entry.slot then
      throwError "ibubble: replay certificate selects multiple bubbles for goal slot {entry.slot}"
    slots := slots.insert entry.slot
  return entries

mutual

/-- Navigate downward through the Rapps selected by a bubble's forward certificate. -/
private partial def followForwardPath (bubble : Bubble) (path : Array RappId)
    (goalRef : GoalRef) (focus : MVarId) (remaining : Array MVarId := #[]) :
    ReplayM (Array MVarId) := do
  let goal ← goalRef.get
  /- No more path to navigate down. -/
  unless path[0]?.isSome do
    match bubble.endKind with
    | .normalization =>
      let (result, normRemaining) ← normalize focus goal
      match result with
      | .proved => return remaining ++ normRemaining
      | _ => throwError "ibubble: normalization did not close bubble {bubble.id} during replay"
    | .ruleApplication => throwError "ibubble: rule bubble {bubble.id} has an empty forward path"
    | .platformEmission _ => throwError "ibubble: platform bubble {bubble.id} has an empty forward path"
  let some rappId := path[0]?
    | throwError "ibubble: the forward path unexpectedly became empty during replay"

  /- Fetch corresponding Rapp node following from current Goal node. -/
  let rappRef ← getRapp rappId
  let rapp ← rappRef.get
  let recordedParent ← rapp.parent.get
  unless recordedParent.id == goal.id do
    throwError "ibubble: forward path selects Rapp {rapp.id} from goal {goal.id}, but its parent is goal {recordedParent.id}"
  let tail := path.extract 1 path.size
  let children? := match bubble.endKind with
    | .normalization => none
    | .ruleApplication => some #[]
    | .platformEmission children => some children

  /- The end of the single-platform chain has not been reached; move down one more step. -/
  if !tail.isEmpty || children?.isNone then
    let (irisGoals, localRemaining) ←
      replayRuleApplication focus goal rappRef #[] 1 (some bubble.consumed)
    let plat ← rapp.children.get
    unless plat.kind.isSingle do throwError
      "ibubble: forward path expected Rapp {rapp.id} to have a single platform"
    let childGoal : GoalRef ← if h : plat.goals.size = 1 then pure plat.goals[0]
      else throwError "ibubble: the forward path expected exactly one child beneath Rapp {rapp.id}, but found {plat.goals.size}"
    return ← followForwardPath bubble tail childGoal irisGoals[0]! (remaining ++ localRemaining)

  /- The final Rapp has been reached; either close the goal directly or enter an
    ordinary/linear platform. -/
  if children?.isSome then
    let chain ← match bubble.endKind with
      | .platformEmission terminals =>
          expandPlatformChildren (← rapp.children.get) terminals
      | .ruleApplication => pure #[]
      | .normalization => pure #[]
    /- Context splits are indexed by the Rapp's original child slots. -/
    let children := (chain.qsort λ left right => left.slot < right.slot).map (·.bubble)
    let (irisGoals, localRemaining) ← replayRuleApplication focus goal rappRef children
    /- Replay follows residual-link order; slots only select the corresponding
    original child goals produced by the Rapp. -/
    let pending ← chain.mapM λ child => do
      let some focus := irisGoals[child.slot]?
        | throwError "ibubble: replay certificate references missing goal slot {child.slot}"
      return (child.bubble, focus)
    let mut allRemaining := remaining ++ localRemaining
    for (bubbleId, focus) in pending do
      allRemaining := allRemaining ++ (← replaySubtree focus bubbleId)
    return allRemaining
  else throwError "ibubble: normalization bubble {bubble.id} unexpectedly reached terminal Rapp {rapp.id}"

/--
  Replay one search subtree from its current Lean goal, using a bubble to
  navigate the selected search-tree path.
-/
private partial def replaySubtree (focus : MVarId) (bubbleId : BubbleId) :
    ReplayM (Array MVarId) := do
  let bubble ← getBubble bubbleId
  trace[ibubble.replay]
    "navigate from the current goal using bubble {bubble.id} at search goal {bubble.goal}"
  let boundaryGoal ← getGoal bubble.goal
  followForwardPath bubble bubble.forward boundaryGoal focus

end

/-- Entry point for the replay procedure. -/
def replayProof (config : SearchConfig) (rootBubble : BubbleId) :
    TreeM (Array MVarId) := do
  let rootRef ← TreeM.getRootGoal
  let root ← rootRef.get
  root.preNormState.restore
  let (remaining, state) ←
    (ReaderT.run (replaySubtree root.preNormGoal rootBubble) { config }).run {}

  /- When suffixed with `?`, the tactic provides a script through the `Try this` interface. -/
  if config.generateScript? then
    /- `evalIBubble` exposes independent goals before goals that depend on other
       metavariables. The replacement script must leave them in that same order. -/
    let dependees ← remaining.foldlM (init := ∅) λ m g => do
      return m ∪ (← g.getMVarDependencies)
    let (dependent, independent) := remaining.partition dependees.contains
    let finalGoals := independent ++ dependent
    let tactics ← state.script.render root.preNormGoal (some finalGoals)
    let ref ← getRef
    addTryThisTacticSeqSuggestion ref tactics
  return remaining

end Bubble.Replay
