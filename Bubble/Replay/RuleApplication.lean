module

public meta import Iris.ProofMode
public meta import Bubble.Replay.Normalization
public meta import Bubble.Search.Names

public meta section

namespace Bubble.Replay

open Lean Lean.Elab.Tactic Lean.Meta
open Iris.ProofMode
open ReplayM

private def appliedHypIdent? : AppliedHyp → Option (TSyntax `ident)
  | .spatial hyp | .intuitionistic hyp => some (mkIdent hyp.name)
  | .lean userName _ => some (mkIdent userName)

private def frameIdent (hyp : IrisHyp) : MetaM (TSyntax `frameIdent) := do
  let name := mkIdent hyp.name
  `(frameIdent| $name:ident)

private def mkSpatialSpecPat (hyps : Array IrisHyp) :
    MetaM (TSyntax `specPat) := do
  let names ← hyps.mapM frameIdent
  `(specPat| [$[$names:frameIdent]*])

private def mkIApply (fn : TSyntax `term)
    (splits : Array (Array IrisHyp)) : MetaM (TSyntax `tactic) := do
  if splits.isEmpty then
    `(tactic| iapply $fn:term)
  else
    let patterns ← splits.mapM mkSpatialSpecPat
    `(tactic| iapply $fn:term $$ $patterns:specPat*)

/-- Reconstruct the Iris tactic corresponding to a recorded rule application. -/
private def mkRuleApplicationTactic (rapp : Rapp)
    (splits : Array (Array IrisHyp)) (childCount : Nat)
    (config : SearchConfig) : MetaM (TSyntax `tactic) := do
  let fallback ← `(tactic| skip)
  match rapp.appliedRule.info.builder with
  | .backward _ =>
      let premiseSplits := splits.extract 0 (splits.size - 1)
      let decl := mkIdent rapp.appliedRule.id.name.eraseMacroScopes
      mkIApply decl premiseSplits
  | .forward => pure fallback
  | .tactic .ipureIntro =>
      if config.pureStop? then `(tactic| ipureintro)
      else
        let solver : TSyntax `tactic := ⟨config.pureSolver⟩
        `(tactic| (ipureintro; $solver:tactic))
  | .tactic .iexist => `(tactic| iexists _)
  | .tactic .icases =>
      match rapp.usedHyp? >>= appliedHypIdent?,
          rapp.generatedSpatialHyps[0]?, rapp.generatedSpatialHyps[1]? with
      | some used, some left, some right =>
          let left := mkIdent left.name.eraseMacroScopes
          let right := mkIdent right.name.eraseMacroScopes
          `(tactic| icases $used:term with ($left:ident | $right:ident))
      | _, _, _ => pure fallback
  | .tactic .icasesFalse =>
      match rapp.usedHyp? >>= appliedHypIdent? with
      | some used => `(tactic| icases $used:term with ⟨⟩)
      | none => pure fallback
  | .tactic .isplit => `(tactic| isplit)
  | .tactic .ileft => `(tactic| ileft)
  | .tactic .iright => `(tactic| iright)
  | .tactic .imodIntro => `(tactic| imodintro)
  | .tactic .imod =>
      match rapp.usedHyp? >>= appliedHypIdent?, rapp.generatedSpatialHyps[0]? with
      | some used, some generated =>
          let generated := mkIdent generated.name.eraseMacroScopes
          `(tactic| imod $used:term with $generated:ident)
      | some used, none => `(tactic| imod $used:term)
      | none, _ => pure fallback
  | .tactic .identity =>
      match splits[0]? with
      | some left =>
          let names := left.map fun hyp => mkIdent hyp.name
          `(tactic| isplitl [$names*])
      | none => pure fallback
  | .tactic .applyHyps =>
      match rapp.usedHyp? >>= appliedHypIdent? with
      | some used =>
          if childCount == 0 then `(tactic| iexact $used:ident)
          else mkIApply used splits
      | none => pure fallback
  | .tactic .haveHyps =>
      match rapp.usedHyp? >>= appliedHypIdent?, rapp.generatedSpatialHyps[0]? with
      | some used, some generated =>
          let generated := mkIdent generated.name.eraseMacroScopes
          let premiseSplits := splits.extract 0 (splits.size - 1)
          if premiseSplits.isEmpty then pure fallback
          else
            let patterns ← premiseSplits.mapM mkSpatialSpecPat
            `(tactic| ihave $generated:ident := $used:term $$ $patterns:specPat*)
      | _, _ => pure fallback

/-- Separate replay-generated Iris goals from ordinary Lean goals. -/
private def classifyGoals (goals : Array MVarId) :
    ReplayM (Array MVarId × Array MVarId) := do
  goals.foldlM (init := (#[], #[])) fun (iris, lean) goal => do
    if ← goal.isAssignedOrDelayedAssigned then return (iris, lean)
    let irisGoal? ← goal.withContext do
      let type ← instantiateMVars (← goal.getType)
      return parseIrisGoal? type
    if irisGoal?.isSome then return (iris.push goal, lean)
    return (iris, lean.push goal)

/--
  Solve an auxiliary term metavariable only when no other open goal refers to it.
  This preserves witnesses that must be inferred by a later Iris subgoal while
  allowing irrelevant witnesses to be recovered from the local Lean context.
-/
private def solveIndependentAuxGoals (irisGoals otherGoals : Array MVarId) :
    ReplayM (Array MVarId) := do
  let allGoals := irisGoals ++ otherGoals
  let mut remaining := #[]
  for goal in otherGoals do
    if ← goal.isAssignedOrDelayedAssigned then continue
    let isPure ← goal.withContext do
      isProp (← instantiateMVars (← goal.getType))
    if isPure then
      remaining := remaining.push goal
      continue
    let referenced ← allGoals.anyM λ other => do
      if other == goal || (← other.isAssignedOrDelayedAssigned) then return false
      return (← other.withContext other.getMVarDependencies).contains goal
    if referenced then
      remaining := remaining.push goal
      continue
    let preState ← liftM (m := MetaM) saveState
    let tactic ← `(tactic| assumption)
    let solved ← try
      let generated ← withSuppressedMessages <| evalTacticAt tactic goal
      let generated ← ReplayM.openGoals generated.toArray
      if (← goal.isAssignedOrDelayedAssigned) && generated.isEmpty then
        let postState ← liftM (m := MetaM) saveState
        ReplayM.appendScript #[{
          preState, preGoal := goal, tactic, postState, postGoals := generated
        }]
        pure true
      else
        preState.restore
        pure false
    catch _ =>
      preState.restore
      pure false
    unless solved do remaining := remaining.push goal
  return remaining

/-- Discharge replay-generated pure Lean goals with the configured solver. -/
private def solvePureGoals (goals : Array MVarId) : ReplayM (Array MVarId) := do
  let config ← ReplayM.getConfig
  let mut remaining := #[]
  for goal in goals do
    if ← goal.isAssignedOrDelayedAssigned then continue
    let isPure ← goal.withContext do
      isProp (← instantiateMVars (← goal.getType))
    if !isPure || config.pureStop? then
      remaining := remaining.push goal
      continue
    let preState ← liftM (m := MetaM) saveState
    let generated ← withSuppressedMessages <|
      evalTacticAt config.pureSolver goal
    let generated ← ReplayM.openGoals generated.toArray
    unless generated.isEmpty do
      throwError "ibubble: pure solver left {generated.size} unresolved replay goal(s)"
    let postState ← liftM (m := MetaM) saveState
    ReplayM.appendScript #[{
      preState, preGoal := goal, tactic := ⟨config.pureSolver⟩,
      postState, postGoals := generated
    }]
  return remaining

/-- Replay one recorded rule application and return its Iris children and unrelated goals. -/
def replayRuleApplication (focus : MVarId) (goal : Goal) (rappRef : RappRef)
    (children : Array BubbleId) (expectedChildren : Nat := children.size)
    (singleChildConsumed? : Option (Array IrisHyp) := none) :
    ReplayM (Array MVarId × Array MVarId) := do
  let (normalizedFocus, normRemaining) ← normalizeForRuleApplication focus goal
  let rapp ← rappRef.get
  let plat ← rapp.children.get
  let unaryApplyHyps := match rapp.appliedRule.info.builder with
    | .tactic .applyHyps => true
    | _ => false
  let unaryContextUsed := singleChildConsumed?.any fun consumed => !consumed.isEmpty
  let config ← ReplayM.getConfig
  let splits ←
    if plat.kind.isLinear && children.size > 1 then
      children.mapM λ id => return (← ReplayM.getBubble id).consumed
    else if config.generateScript? && plat.kind.isSingle && expectedChildren == 1 &&
        unaryApplyHyps && unaryContextUsed then
      /- A unary `iapply` still benefits from an explicit context. Since its
      sole child receives the whole remaining spatial context, reconstruct
      that context directly and omit any spatial hypothesis consumed by the
      application itself. -/
      let spatial ← Bubble.Search.spatialHypsOf normalizedFocus
      let usedName? : Option Name := match rapp.usedHyp? with
        | some (.spatial hyp) | some (.intuitionistic hyp) => some hyp.name
        | some (.lean userName _) => some userName
        | none => none
      pure #[spatial.filter λ hyp =>
        let name := hyp.name.eraseMacroScopes
        usedName?.all (·.eraseMacroScopes != name)]
    else
      pure #[]
  let plainTactic ← mkRuleApplicationTactic rapp #[] expectedChildren config
  /- A unary specialization can make the replayed script substantially more
  informative, but it is not interchangeable with a bare `iapply`: in
  particular, it may specialize a wand before a surrounding modality has been
  handled.  Try the more explicit form in an isolated metavariable state and
  keep it only when it produces the same number of Iris child goals. -/
  let explicitUnary :=
    config.generateScript? && plat.kind.isSingle && expectedChildren == 1 &&
      unaryApplyHyps && unaryContextUsed
  let tactic ← if !explicitUnary then
    mkRuleApplicationTactic rapp splits expectedChildren config
  else
    let candidate ← mkRuleApplicationTactic rapp splits expectedChildren config
    let probeState ← liftM (m := MetaM) saveState
    let accepted ← try
      let generated ← withSuppressedMessages <| evalTacticAt candidate normalizedFocus
      let generated ← ReplayM.openGoals generated.toArray
      let (irisGoals, _) ← classifyGoals generated
      pure (irisGoals.size == expectedChildren)
    catch _ => pure false
    probeState.restore
    pure (if accepted then candidate else plainTactic)
  trace[ibubble.replay]
    "Rapp {rapp.id}, rule {rapp.appliedRule.id}: {tactic}"
  let preState ← liftM (m := MetaM) saveState
  let generated ← withSuppressedMessages <|
    evalTacticAt tactic normalizedFocus
  let generated ← ReplayM.openGoals generated.toArray
  let postState ← liftM (m := MetaM) saveState
  ReplayM.appendScript #[{
    preState, preGoal := normalizedFocus, tactic, postState, postGoals := generated
  }]
  let (irisGoals, leanGoals) ← classifyGoals generated
  let leanGoals ← solveIndependentAuxGoals irisGoals leanGoals
  let leanGoals ← solvePureGoals leanGoals
  if irisGoals.size != expectedChildren then
    throwError "ibubble: replay of Rapp {rapp.id} produced {irisGoals.size} Iris goals, expected {expectedChildren}"
  return (irisGoals, normRemaining ++ leanGoals)

end Bubble.Replay
