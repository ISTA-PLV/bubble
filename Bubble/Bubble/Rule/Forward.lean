-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.HaveHyps

public meta section

namespace Bubble.Forward

open Lean Elab Tactic Meta Qq Iris.ProofMode

initialize registerTraceClass `ibubble.forward

/- Instantiate a forward theorem and bridge its statement into an Iris proposition. -/
private def instantiateTheorem? (irisGoal : IrisGoal) (decl : Name) :
    MetaM (Option Q($irisGoal.prop)) := do
  let { prop, bi, .. } := irisGoal
  let theoremType ← inferType (← mkConstWithFreshMVarLevels decl)
  let (args, binderInfos, type) ← forallMetaTelescope theoremType
  unless ← Meta.isProp type do return none
  have type : Q(Prop) := type
  let hyp ← mkFreshExprMVarQ prop
  let .some _ ← Bubble.Tactic.trySynthInstanceProbeQ
      q(AsEmpValid .into $type .in $prop $bi $hyp)
    | return none
  for arg in args, binderInfo in binderInfos do
    if binderInfo.isInstImplicit && !(← arg.mvarId!.isAssigned) then
      let some inst ← (try synthInstance? (← inferType arg) catch _ => pure none)
        | return none
      unless ← isDefEq arg inst do return none
  return some (← instantiateMVars hyp)

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  input.goal.withContext do
    let some irisGoal ← Bubble.Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
    let decl := input.matchResult.rule.id.name
    let some hyp ← instantiateTheorem? irisGoal decl
      | trace[ibubble.forward] "forward {decl}: statement is not an Iris entailment"
        input.state.restore
        return RuleOutput.ofSpecs #[]
    /- Like `haveHyps`, but the theorem is persistent and is not removed from the context. -/
    let (premises, conclusion) :=
      (← Bubble.Tactic.HaveHyps.parseHypothesis? (bi := irisGoal.bi) q(true) hyp).getD
        (#[], hyp)
    let (goals, generatedHyp?) ←
      Bubble.Tactic.HaveHyps.mkChildren irisGoal (← input.goal.getTag) input.depth
        irisGoal.hyps premises conclusion
    return .ofSpec {
      goals
      postState := ← Meta.saveState
      effect := {
        generatedSpatialHyps := generatedHyp?.toArray
        multiGoalAction? := if goals.size > 1 then some .partitionContext else none
      }
    }

end Bubble.Forward
