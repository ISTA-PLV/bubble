module

public meta import Batteries.Data.Array.Basic
public meta import Lean.Data.Name
public meta import Bubble.Index.Types
public meta import Bubble.Util.Percent

public meta section

open Lean Lean.Meta

namespace Bubble

inductive RulePhase
  | norm
  | expand
  deriving Inhabited, BEq, Hashable, Ord

namespace RulePhase

instance : ToString RulePhase where
  toString
    | norm => "norm"
    | expand => "expand"

end RulePhase

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

/- User-facing rule categories used by attributes and local configuration. -/
inductive RuleBuilderKind
  | apply
  | backward
  | forward
  | simp
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilderKind

instance : ToString RuleBuilderKind where
  toString
    | apply => "apply"
    | backward => "backward"
    | forward => "forward"
    | simp => "simp"

end RuleBuilderKind

/-- The application selected when a theorem is registered as a backward rule. -/
inductive BackwardRuleForm
  | direct
  | mp
  | mpr
  deriving Inhabited, BEq, Hashable, Ord

namespace BackwardRuleForm

instance : ToString BackwardRuleForm where
  toString
    | .direct => "direct"
    | .mp => "mp"
    | .mpr => "mpr"

end BackwardRuleForm

/-- A built-in proof-mode expansion. -/
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

/-- Executable rule descriptor.  `RuleBuilderKind` remains the user-facing
classification stored in `RuleId`; this type says how a selected rule runs. -/
inductive RuleBuilder where
  | tactic (descr : TacticDescr)
  | backward (form : BackwardRuleForm := .direct)
  | forward
  deriving Inhabited, BEq, Hashable, Ord

namespace RuleBuilder

instance : ToString RuleBuilder where
  toString
    | .tactic descr => s!"tactic {descr}"
    | .backward form => s!"backward {form}"
    | .forward => "forward"

end RuleBuilder

structure RuleId where
  name : Name
  kind : RuleBuilderKind
  phase : RulePhase
  scope : RuleScope
  variant : Nat := 0
  deriving Inhabited, BEq, Hashable

namespace RuleId

protected def compare : RuleId → RuleId → Ordering :=
  compareLex (compareOn (·.kind)) $
  compareLex (compareOn (·.phase)) $
  compareLex (compareOn (·.scope)) $
  compareLex (λ r₁ r₂ => r₁.name.cmp r₂.name) $
  compareOn (·.variant)

instance : Ord RuleId where
  compare := RuleId.compare

instance : ToString RuleId where
  toString r :=
    let suffix := if r.variant == 0 then "" else s!"|{r.variant}"
    s!"{r.phase}|{r.kind}|{r.scope}|{r.name}{suffix}"

end RuleId

inductive DisplayRuleId
  | ruleId (id : RuleId)
  | normSimp
  deriving Inhabited, BEq, Hashable, Ord

namespace DisplayRuleId

instance : ToString DisplayRuleId where
  toString
    | ruleId n => toString n
    | normSimp => "<norm simp>"

end DisplayRuleId

structure RuleInfo where
  builder : RuleBuilder
  successProbability : Percent := .hundred
  deriving Inhabited, BEq

namespace RuleInfo

protected def compare (left right : RuleInfo) : Ordering :=
  (compare right.successProbability left.successProbability).then
    (compare left.builder right.builder)

instance : Ord RuleInfo where
  compare := RuleInfo.compare

instance : Hashable RuleInfo where
  hash info := hash info.builder

instance : ToFormat RuleInfo where
  format info := Std.Format.text (toString info.builder)

def ofBuilder (builder : RuleBuilder)
    (successProbability : Percent := .hundred) : RuleInfo where
  builder
  successProbability

end RuleInfo

structure Rule (α : Type) where
  id : RuleId
  indexingMode : IndexingMode
  info : α
  deriving Inhabited

namespace Rule

instance : BEq (Rule α) where
  beq left right := left.id == right.id

instance : Ord (Rule α) where
  compare left right := compare left.id right.id

instance : Hashable (Rule α) where
  hash rule := hash rule.id

def compareByPriority [Ord α] (left right : Rule α) : Ordering :=
  compare left.info right.info

def compareById (left right : Rule α) : Ordering :=
  left.id.compare right.id

def compareByPriorityThenName [Ord α] (left right : Rule α) : Ordering :=
  (compareByPriority left right).then (compareById left right)

@[inline]
protected def map (f : α → β) (rule : Rule α) : Rule β :=
  { rule with info := f rule.info }

@[inline]
protected def mapM [Monad m] (f : α → m β) (rule : Rule α) : m (Rule β) := do
  return { rule with info := ← f rule.info }

end Rule

abbrev RuleMatch := IndexMatchResult (Rule RuleInfo)

abbrev RuleQueue := Subarray RuleMatch

namespace RuleQueue

instance : EmptyCollection RuleQueue :=
  inferInstanceAs $ EmptyCollection (Subarray _)

instance : Inhabited RuleQueue :=
  inferInstanceAs $ Inhabited (Subarray _)

def ofArray (matchResults : Array RuleMatch) : RuleQueue :=
  matchResults.toSubarray

def pop? (queue : RuleQueue) : Option (RuleMatch × RuleQueue) :=
  Subarray.popHead? queue

end RuleQueue

end Bubble
