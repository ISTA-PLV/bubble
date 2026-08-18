module

public meta import Bubble.Frontend.Attribute
public meta import Bubble.Index.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble.Rule

open Lean Meta

private def builtinRule (name : Name) (kind : RuleBuilderKind)
    (descr : TacticDescr) (probability : Percent) : Rule RuleInfo where
  id := { name, kind, phase := .expand, scope := .global }
  indexingMode := .unindexed
  info := .ofBuilder (.tactic descr) probability

def identityRule : Rule RuleInfo :=
  builtinRule `identity .forward .identity .almost

def applyHypsRule : Rule RuleInfo :=
  builtinRule `applyHyps .apply .applyHyps .high

def haveHypsRule : Rule RuleInfo :=
  builtinRule `haveHyps .forward .haveHyps .almost

def icasesRule : Rule RuleInfo :=
  builtinRule `icases .forward .icases .almost

def icasesFalseRule : Rule RuleInfo :=
  builtinRule `icasesFalse .forward .icasesFalse ⟨0.1⟩

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
  builtinRule `imod .apply .imod .high

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
    (decl : Name) (probability : Percent) : Rule RuleInfo where
  id := { name := decl, kind, phase := .expand, scope }
  indexingMode := .unindexed
  info := .ofBuilder
    (match kind with
      | .backward => .backward
      | .forward => .forward
      | _ => .forward)
    probability

private def overridden (localRules : Array LocalTheoremRule)
    (kind : RuleBuilderKind) (decl : Name) : Bool :=
  localRules.any fun rule => rule.kind == kind && rule.decl == decl

def backwardIndex (localRules : Array LocalTheoremRule := #[]) :
    MetaM (Index RuleInfo) := do
  let mut index : Index RuleInfo := {}
  for entry in ← getIbubbleBackwardLemmas do
    unless overridden localRules .backward entry.decl do
      let rule := theoremRule .global .backward entry.decl entry.successProbability
      index := index.add rule rule.indexingMode
  return index

def localTheoremIndex (rules : Array LocalTheoremRule) :
    MetaM (Index RuleInfo) := do
  let mut index : Index RuleInfo := {}
  for localRule in rules do
    match localRule.action with
    | .erase => pure ()
    | .insert probability =>
        let rule := theoremRule .local localRule.kind localRule.decl probability
        index := index.add rule rule.indexingMode
  return index

def buildIndex (config : SearchConfig) : MetaM (Index RuleInfo) := do
  return commonIndex.merge (← backwardIndex config.localTheoremRules)
    |>.merge (← localTheoremIndex config.localTheoremRules)

end Bubble.Rule
