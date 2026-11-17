-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean.Parser.Tactic
public import Bubble.Util.Percent
public import Bubble.Rule.Types

public meta section

namespace Bubble

open Lean Meta

/- Search strategies supported by `ibubble`. -/
inductive Strategy
  | bestFirst
  | depthFirst
  | breadthFirst
  deriving Inhabited, BEq, Repr

/-- Default solver used for pure Lean goals produced by `ipureintro`. -/
def defaultPureSolver : Syntax :=
  .node .none ``_root_.Lean.Parser.Tactic.assumption #[.atom .none "assumption"]

inductive LocalRuleAction where
  | insert (prob : Percent)
  | erase
  deriving Inhabited

/-- The direction in which a theorem is used by local rule configuration. -/
inductive RuleDirection where
  | backward
  | forward
  deriving Inhabited, BEq

/- A theorem rule added for a single `ibubble` invocation. -/
structure LocalTheoremRule where
  direction : RuleDirection
  decl : Name
  action : LocalRuleAction
  deriving Inhabited

def defaultMaxTheoremUses : Nat := 2

structure SearchConfig where
  /- maximum depth of the search tree -/
  maxDepth : Nat := 100
  /- maximum number of uses of one theorem along a search branch -/
  maxTheoremUses : Nat := defaultMaxTheoremUses
  /- maximum rapp children for each goal -/
  maxRappNumber : Nat := 30
  /- maximum normalization iteration for each goal -/
  maxNormIterations : Nat := 20
  /- search strategy used during search (default: bestFirst) -/
  strategy : Strategy := Strategy.bestFirst
  /- whether generated script after proven (default: false) -/
  generateScript? : Bool := false
  /- whether to enable the simplifier during normalization (default: true) -/
  enableSimp? : Bool := true
  /- Solver run on pure Lean goals produced by `ipureintro`. -/
  pureSolver : Syntax := defaultPureSolver
  /- Stop search at pure Iris goals and expose their Lean propositions. -/
  pureStop? : Bool := false
  /- Theorem-rule changes applied only for this `ibubble` invocation. -/
  localTheoremRules : Array LocalTheoremRule := #[]

end Bubble
