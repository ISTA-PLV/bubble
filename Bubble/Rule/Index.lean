module

public meta import Bubble.Frontend.Attribute
public meta import Bubble.Index.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble.Rule

open Lean Meta
open Iris.BI

private def builtinRule (name : Name) (kind : RuleBuilderKind)
    (descr : TacticDescr) (probability : Percent) : Rule RuleInfo where
  id := { name, kind, phase := .expand, scope := .global }
  indexingMode := .unindexed
  info := .ofBuilder (.tactic descr) probability

def identityRule : Rule RuleInfo :=
  builtinRule `identity .forward .identity .medium

def applyHypsRule : Rule RuleInfo :=
  builtinRule `applyHyps .apply .applyHyps .high

def haveHypsRule : Rule RuleInfo :=
  builtinRule `haveHyps .forward .haveHyps .medium

def icasesRule : Rule RuleInfo :=
  builtinRule `icases .forward .icases .low

def icasesFalseRule : Rule RuleInfo :=
  builtinRule `icasesFalse .forward .icasesFalse .almost

def ipureIntroRule : Rule RuleInfo :=
  builtinRule `ipureIntro .apply .ipureIntro .high

def ileftRule : Rule RuleInfo :=
  builtinRule `ileft .apply .ileft .high

def irightRule : Rule RuleInfo :=
  builtinRule `iright .apply .iright .high

def iexistRule : Rule RuleInfo :=
  builtinRule `iexist .apply .iexist .almost

def imodIntroRule : Rule RuleInfo :=
  builtinRule `imodIntro .apply .imodIntro .medium

def imodRule : Rule RuleInfo :=
  builtinRule `imod .apply .imod .low

def isplitRule : Rule RuleInfo :=
  builtinRule `isplit .apply .isplit .almost

def commonIndex : Index RuleInfo :=
  ({} : Index RuleInfo)
    |>.add identityRule identityRule.indexingMode
    |>.add applyHypsRule applyHypsRule.indexingMode
    |>.add haveHypsRule haveHypsRule.indexingMode
    |>.add icasesRule icasesRule.indexingMode
    |>.add icasesFalseRule icasesFalseRule.indexingMode
    |>.add ipureIntroRule ipureIntroRule.indexingMode
    |>.add ileftRule ileftRule.indexingMode
    |>.add irightRule irightRule.indexingMode
    |>.add iexistRule iexistRule.indexingMode
    |>.add imodIntroRule imodIntroRule.indexingMode
    |>.add imodRule imodRule.indexingMode
    |>.add isplitRule isplitRule.indexingMode

private def theoremRule (scope : RuleScope) (kind : RuleBuilderKind)
    (decl : Name) (probability : Percent)
    (form : BackwardRuleForm := .direct) (variant : Nat := 0)
    (indexingMode : IndexingMode := .unindexed) : Rule RuleInfo where
  id := { name := decl, kind, phase := .expand, scope, variant }
  indexingMode
  info := .ofBuilder
    (match kind with
      | .backward => .backward form
      | .forward => .forward
      | _ => .forward)
    probability

/-- Lower a registered bi-entailment into two explicitly oriented backward rules. -/
private def backwardTheoremRules (scope : RuleScope) (decl : Name)
    (probability : Percent) : MetaM (Array (Rule RuleInfo)) := do
  let info ← getConstInfo decl
  let (_, _, body) ← forallMetaTelescopeReducing info.type
  let body ← whnf body
  let some args := body.appM? ``BIBase.BiEntails
    | return #[theoremRule scope .backward decl probability]
  let some lhs := args[args.size - 2]? | return #[]
  let some rhs := args[args.size - 1]? | return #[]
  let mpMode ← IndexingMode.targetMatching rhs
  let mprMode ← IndexingMode.targetMatching lhs
  return #[
    theoremRule scope .backward decl probability .mp 1 mpMode,
    theoremRule scope .backward decl probability .mpr 2 mprMode
  ]

def backwardIndex (localRules : Array LocalTheoremRule := #[]) :
    MetaM (Index RuleInfo) := do
  (← getIbubbleBackwardLemmas).foldlM (init := {}) λ index entry => do
    if localRules.any λ rule => rule.kind == .backward && rule.decl == entry.decl then
      return index
    return (← backwardTheoremRules .global entry.decl entry.successProbability).foldl
      (init := index) λ index rule => index.add rule rule.indexingMode

def localTheoremIndex (rules : Array LocalTheoremRule) :
    MetaM (Index RuleInfo) := do
  let mut index : Index RuleInfo := {}
  for localRule in rules do
    match localRule.action with
    | .erase => pure ()
    | .insert probability =>
      if localRule.kind == .backward then
        for rule in ← backwardTheoremRules .local localRule.decl probability do
          index := index.add rule rule.indexingMode
      else
        let rule := theoremRule .local localRule.kind localRule.decl probability
        index := index.add rule rule.indexingMode
  return index

def buildIndex (config : SearchConfig) : MetaM (Index RuleInfo) := do
  return commonIndex.merge (← backwardIndex config.localTheoremRules)
    |>.merge (← localTheoremIndex config.localTheoremRules)

end Bubble.Rule
