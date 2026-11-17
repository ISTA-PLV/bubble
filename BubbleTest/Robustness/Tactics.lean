module

public meta import Aesop
public meta import BubbleTest.Robustness.RuleSet
public meta import Iris.ProofMode
public meta import BubbleTest.Robustness.Timing

public meta section

namespace BubbleTest.Robustness

open Lean Lean.Elab Tactic Meta Qq
open Iris Iris.ProofMode

private def runTacticApplications (input : Aesop.RuleTacInput)
    (tactics : Array (TSyntax `tactic)) : Aesop.BaseM Aesop.RuleTacOutput := do
  let mut applications := #[]
  for tactic in tactics do
    let initialState ← saveState
    try
      let output ← Aesop.RuleTac.ofTacticSyntax (fun _ => pure tactic) input
      applications := applications ++ output.applications
    catch _ =>
      pure ()
    finally
      restoreState initialState
  return ⟨applications⟩

/-- Introduce one separating implication into the spatial context. -/
@[aesop safe -200 tactic (rule_sets := [irisNaive])]
meta def intros : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    runTacticApplications input #[← `(tactic| iintro Hrobustness)]

/-- Flatten one separating-conjunction hypothesis before search choices are made. -/
@[aesop safe -150 tactic (rule_sets := [irisNaive])]
meta def destructSeps : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let target ← input.goal.getType
    let some irisGoal := parseIrisGoal? target | return ⟨#[]⟩
    for ivar in irisGoal.hyps.spatialIVarIds .topToBottom do
      let some name := irisGoal.hyps.getUserName? ivar | continue
      let term : TSyntax `term := ⟨(mkIdent name).raw⟩
      let pmt ← `(pmTerm| $term:term)
      let output ← runTacticApplications input #[← `(tactic| icases $pmt with ⟨_, _⟩)]
      if !output.applications.isEmpty then
        return output
    return ⟨#[]⟩

/-- Close an Iris Proof Mode goal using a matching spatial or persistent hypothesis. -/
@[aesop safe -100 tactic (rule_sets := [irisNaive])]
meta def assumption : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    runTacticApplications input #[← `(tactic| iassumption)]

/-- Try propositional Lean hypotheses as Iris rules, as Bubble does. -/
@[aesop 70% tactic (rule_sets := [irisNaive])]
meta def applyHyps : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let mut tactics := #[]
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail || localDecl.userName.isAnonymous then
        continue
      unless ← isProp localDecl.type do continue
      let term : TSyntax `term := ⟨(mkIdent localDecl.userName).raw⟩
      let pmt ← `(pmTerm| $term:term)
      tactics := tactics.push (← `(tactic| iapply $pmt))
    runTacticApplications input tactics

private def canSplit (irisGoal : IrisGoal) : MetaM Bool :=
  withoutModifyingState do
    let { prop, bi := _bi, goal, .. } := irisGoal
    let left ← mkFreshExprMVarQ prop
    let right ← mkFreshExprMVarQ prop
    try
      match ← Iris.ProofMode.trySynthInstanceQ q(FromSep $goal $left $right) with
      | .some _ => return true
      | _ => return false
    catch _ => return false

private partial def splitApplications (input : Aesop.RuleTacInput)
    (remaining : List Name) (chosen : Array Name) : Aesop.BaseM (Array Aesop.RuleApplication) := do
  match remaining with
  | [] =>
      let names := chosen.map mkIdent
      let output ← runTacticApplications input #[← `(tactic| isplitl [$names*])]
      return output.applications
  | name :: remaining =>
      let without ← splitApplications input remaining chosen
      let withName ← splitApplications input remaining (chosen.push name)
      return without ++ withName

/-- Generate every eager spatial-context split as a separate Aesop alternative. -/
@[aesop 60% tactic (rule_sets := [irisNaive])]
meta def enumerateSplits : Aesop.RuleTac := fun input =>
  input.goal.withContext do
    let target ← input.goal.getType
    let some irisGoal := parseIrisGoal? target | return ⟨#[]⟩
    -- Check applicability once, before enumerating 2^n partitions. In
    -- particular, atomic goals must not pay the enumeration cost.
    unless ← canSplit irisGoal do return ⟨#[]⟩
    let names := (irisGoal.hyps.spatialIVarIds .topToBottom).filterMap irisGoal.hyps.getUserName?
    return ⟨← splitApplications input names #[]⟩

/-- Aesop with exhaustive eager enumeration of all `2^n` context splits. -/
elab "inaive" : tactic => do
  let (goal, _) ← ProofMode.startProofMode (← getMainGoal)
  replaceMainGoal [goal]
  evalTactic <| ← `(tactic|
    aesop (rule_sets := [-builtin, -default, irisNaive])
      (config := {
        terminal := true
        maxRuleApplicationDepth := 0
        maxRuleApplications := 0
        enableSimp := false
        enableUnfold := false
      }))

/-- A mnemonic alias for the exhaustive Aesop baseline. -/
macro "iaesop" : tactic => `(tactic| inaive)

end BubbleTest.Robustness
