module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Rule.Tactic.IMod

open Lean Elab Tactic Meta
open Iris.ProofMode

private structure Candidate where
  name : Name
  applied : AppliedHyp

private partial def candidates {u prop bi} :
    ∀ {e}, @Hyps u prop bi e → Array Candidate
  | _, .emp _ => #[]
  | _, .hyp _ name ivar persistent _ _ =>
      let hyp : IrisHyp := { name, ivar }
      #[{ name, applied := if Iris.ProofMode.isTrue persistent then
          .intuitionistic hyp else .spatial hyp }]
  | _, .sep _ _ _ _ left right => candidates left ++ candidates right

/--
  Reject modal eliminations which neither refine an incoming
  metavariable nor change the Iris context or target.
-/
private def madeProgress (input : RuleInput) (pre post : IrisGoal) : MetaM Bool := do
  if ← input.mvars.anyM (·.isAssignedOrDelayedAssigned) then return true
  withoutModifyingState do
    try
      let sameHyps ← isDefEq (← instantiateMVars pre.e) (← instantiateMVars post.e)
      if !sameHyps then return true
      return !(← isDefEq (← instantiateMVars pre.goal) (← instantiateMVars post.goal))
    catch _ =>
      return true

def run (input : RuleInput) : TacticM RuleOutput := do
  input.state.restore
  let some preGoal ← Tactic.irisGoal? input.goal | return RuleOutput.ofSpecs #[]
  let allCandidates := candidates preGoal.hyps
  let mut specs := #[]
  for candidate in allCandidates do
    input.state.restore
    let ident := mkIdent candidate.name
    let tactic ← `(tactic| imod $ident:ident)
    try
      let generated ← withSuppressedMessages <| evalTacticAt tactic input.goal
      let some child ← generated.findM? fun goal => do
          return !(← goal.isAssignedOrDelayedAssigned) &&
            Option.isSome (← Tactic.irisGoal? goal)
        | continue
      let some childIrisGoal ← Tactic.irisGoal? child | continue
      unless ← madeProgress input preGoal childIrisGoal do
        trace[ibubble.rule] "imod {candidate.name} made no progress; discarding candidate"
        continue
      let (_, generatedHyps) ← Tactic.spatialDiff preGoal childIrisGoal
      let child ← SubGoal.ofMVar child
      specs := specs.push {
        goals := #[child]
        postState := ← Meta.saveState
        effect := {
          usedHyps := #[candidate.applied]
          generatedSpatialHyps := generatedHyps
        }
      }
    catch exception =>
      trace[ibubble.rule] "imod {candidate.name} failed: {exception.toMessageData}"
  return .ofSpecs specs

end Bubble.Rule.Tactic.IMod
