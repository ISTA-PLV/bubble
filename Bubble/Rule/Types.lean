-- SPDX-License-Identifier: Apache-2.0
module

public import Lean.Data.Name
public meta import Bubble.Util.Percent
public meta import Batteries.Data.Array.Basic
public meta import Bubble.Index.Types

public meta section

open Lean Lean.Meta

namespace Bubble

/-- Whether a rule is globally available or supplied for a single invocation. -/
inductive RuleScope
  | global
  | «local»
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleScope

instance : ToString RuleScope where
  toString
    | global => "global"
    | «local» => "local"

end RuleScope

/-- Whether a theorem is applied directly or through either direction of a bi-entailment. -/
inductive TheoremApplyForm
  | direct
  | mp
  | mpr
  deriving Inhabited, BEq, Hashable, Ord

namespace TheoremApplyForm

instance : ToString TheoremApplyForm where
  toString
    | .direct => "direct"
    | .mp => "mp"
    | .mpr => "mpr"

end TheoremApplyForm

/-- Descriptor for built-in tactics. -/
inductive TacticDescr where
  | identity
  | applyHyps
  | haveHyps
  | icases
  | icasesFalse
  | ipureIntro
  | ileft
  | iright
  | iexist
  | imodIntro
  | imod
  | isplit
  deriving Inhabited, BEq, Hashable, Ord

namespace TacticDescr

instance : ToString TacticDescr where
  toString
    | .identity => "identity"
    | .applyHyps => "applyHyps"
    | .haveHyps => "haveHyps"
    | .icases => "icases"
    | .icasesFalse => "icasesFalse"
    | .ipureIntro => "ipureIntro"
    | .ileft => "ileft"
    | .iright => "iright"
    | .iexist => "iexist"
    | .imodIntro => "imodIntro"
    | .imod => "imod"
    | .isplit => "isplit"

end TacticDescr

/-- Describes the tactic or theorem application performed by a rule. -/
inductive RuleBuilder where
  | tactic (descr : TacticDescr)
  | backward (form : TheoremApplyForm := .direct)
  | forward (form : TheoremApplyForm := .direct)
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilder

instance : ToString RuleBuilder where
  toString
    | .tactic descr => s!"tactic {descr}"
    | .backward form => s!"backward {form}"
    | .forward form => s!"forward {form}"

end RuleBuilder

/-- Identifies a rule by its name, executable descriptor, and scope. -/
structure RuleId where
  name : Name
  builder : RuleBuilder
  scope : RuleScope
  deriving Inhabited, BEq, Hashable

namespace RuleId

protected def compare : RuleId → RuleId → Ordering :=
  compareLex (compareOn (·.builder)) <|
  compareLex (compareOn (·.scope)) <|
  λ r₁ r₂ => r₁.name.cmp r₂.name

instance : Ord RuleId where
  compare := RuleId.compare

instance : ToString RuleId where
  toString r := s!"{r.builder}|{r.scope}|{r.name}"

end RuleId

/-- A rule together with its indexing information and search priority. -/
structure Rule where
  id : RuleId
  indexingMode : IndexingMode
  successProb : Percent := .hundred
  deriving Inhabited

namespace Rule

instance : BEq Rule where
  beq left right := left.id == right.id

instance : Ord Rule where
  compare left right := compare left.id right.id

instance : Hashable Rule where
  hash rule := hash rule.id

def compareByPriority (left right : Rule) : Ordering :=
  compare right.successProb left.successProb

def compareById (left right : Rule) : Ordering :=
  compare left.id right.id

def compareByPriorityThenName (left right : Rule) : Ordering :=
  (compareByPriority left right).then (compareById left right)

end Rule

/-- A rule selected by the index, together with its match locations. -/
abbrev RuleMatch := IndexMatchResult Rule

/-- The remaining rule matches to try for a goal, in search order. -/
abbrev RuleQueue := Subarray RuleMatch

namespace RuleQueue

instance : EmptyCollection RuleQueue :=
  inferInstanceAs $ EmptyCollection (Subarray _)

instance : Inhabited RuleQueue :=
  inferInstanceAs $ Inhabited (Subarray _)

/-- Create a rule queue preserving the array's order. -/
def ofArray (matchResults : Array RuleMatch) : RuleQueue :=
  matchResults.toSubarray

/-- Return the next match and remaining queue, or `none` if the queue is empty. -/
def pop? (queue : RuleQueue) : Option (RuleMatch × RuleQueue) :=
  Subarray.popHead? queue

end RuleQueue

end Bubble
