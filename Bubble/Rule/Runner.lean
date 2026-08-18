module

public meta import Iris.ProofMode.Expr
public meta import Bubble.Core.TreeM
public meta import Bubble.Search.Configure

public meta section

namespace Bubble

open Lean Meta Elab Tactic
open Iris.ProofMode

structure RuleInput where
  goal : MVarId
  depth : Nat
  mvars : Array MVarId
  state : Meta.SavedState
  matchResult : RuleMatch
  config : SearchConfig

structure SubGoal where
  goal : MVarId
  dependencies : Std.HashSet MVarId
  deriving Inhabited

namespace SubGoal

/-- Capture a child goal together with its current metavariable dependencies. -/
def ofMVar (goal : MVarId) : MetaM SubGoal := do
  return { goal, dependencies := ← goal.withContext goal.getMVarDependencies }

end SubGoal

inductive RuleAction where
  | shareContext
  | partitionContext

structure RuleEffect where
  generatedSpatialHyps : Array IrisHyp := #[]
  usedHyps : Array AppliedHyp := #[]
  multiGoalAction? : Option RuleAction := none

structure RappSpec where
  goals : Array SubGoal
  postState : Meta.SavedState
  effect : RuleEffect

structure RuleOutput where
  rappSpecs : Array RappSpec := #[]

namespace RuleOutput

instance : EmptyCollection RuleOutput where
  emptyCollection := { rappSpecs := #[] }

def ofSpec (spec : RappSpec) : RuleOutput :=
  { rappSpecs := #[spec] }

def ofSpecs (specs : Array RappSpec) : RuleOutput :=
  { rappSpecs := specs }

def ofEffect (postState : Meta.SavedState) (effect : RuleEffect)
    (goals : Array SubGoal := #[]) : RuleOutput :=
  .ofSpec { goals, postState, effect }

end RuleOutput

abbrev RuleRunner := RuleInput → TacticM RuleOutput

def mkRuleInput (config : SearchConfig) (parentRef : GoalRef)
    (matchResult : RuleMatch) : TreeM (Option RuleInput) := do
  let parent ← parentRef.get
  let ruleName := toString matchResult.rule.id
  let (goal, state) ← match parent.normalizationState with
    | .normal postGoal postState .. => pure (postGoal, postState)
    | .provenByNorm .. =>
        throwError "ibubble: rule {ruleName} was run on a goal closed by normalization"
    | .notNormal =>
        throwError "ibubble: rule {ruleName} was run on a non-normalized goal"
  let previousState ← Meta.saveState
  state.restore
  let mvars := (← goal.withContext goal.getMVarDependencies).toArray
  previousState.restore
  return some { goal, depth := parent.depth, mvars, state, matchResult, config }

end Bubble
