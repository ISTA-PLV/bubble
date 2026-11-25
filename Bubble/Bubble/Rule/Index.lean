-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Frontend.Attribute
public meta import Bubble.Index.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble

open Lean Meta Iris.BI

/-- Built-in tactic rules. -/
private def builtinRule (name : Name) (descr : TacticDescr) (probability : Percent) : Rule where
  id := { name, builder := .tactic descr, scope := .global }
  indexingMode := .unindexed
  successProb := probability

def identityRule : Rule :=
  builtinRule `identity .identity .medium

def applyHypsRule : Rule :=
  builtinRule `applyHyps .applyHyps .high

def haveHypsRule : Rule :=
  builtinRule `haveHyps .haveHyps .medium

def icasesRule : Rule :=
  builtinRule `icases .icases .low

def icasesFalseRule : Rule :=
  builtinRule `icasesFalse .icasesFalse .almost

def ipureIntroRule : Rule :=
  builtinRule `ipureIntro .ipureIntro .high

def ileftRule : Rule :=
  builtinRule `ileft .ileft .high

def irightRule : Rule :=
  builtinRule `iright .iright .high

def iexistRule : Rule :=
  builtinRule `iexist .iexist .almost

def imodIntroRule : Rule :=
  builtinRule `imodIntro .imodIntro .medium

def imodRule : Rule :=
  builtinRule `imod .imod .low

def isplitRule : Rule :=
  builtinRule `isplit .isplit .almost

def tacticsIndex : Index :=
  ({} : Index)
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

private def theoremRule (scope : RuleScope) (direction : RuleDirection)
    (decl : Name) (probability : Percent)
    (form : TheoremApplyForm := .direct)
    (indexingMode : IndexingMode := .unindexed) : Rule where
  id := {
    name := decl
    builder := match direction with
      | .backward => .backward form
      | .forward => .forward form
    scope
  }
  indexingMode
  successProb := probability

/-- Lower a registered bi-entailment into two explicitly oriented backward rules. -/
private def backwardTheoremRules (scope : RuleScope) (decl : Name)
    (probability : Percent) : MetaM (Array Rule) := do
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
    theoremRule scope .backward decl probability .mp mpMode,
    theoremRule scope .backward decl probability .mpr mprMode
  ]

def backwardIndex (localRules : Array LocalTheoremRule := #[]) :
    MetaM Index := do
  (← getIbubbleBackwardLemmas).foldlM (init := {}) λ index entry => do
    if localRules.any λ rule => rule.direction == .backward && rule.decl == entry.decl then
      return index
    return (← backwardTheoremRules .global entry.decl entry.successProbability).foldl
      (init := index) λ index rule => index.add rule rule.indexingMode

def localTheoremIndex (rules : Array LocalTheoremRule) :
    MetaM Index := do
  let mut index : Index := {}
  for localRule in rules do
    match localRule.action with
    | .erase => pure ()
    | .insert probability =>
      if localRule.direction == .backward then
        for rule in ← backwardTheoremRules .local localRule.decl probability do
          index := index.add rule rule.indexingMode
      else
        let rule := theoremRule .local localRule.direction localRule.decl probability
        index := index.add rule rule.indexingMode
  return index

/-- Return back all potential rules' set in `Bubble`. -/
def buildIndex (config : SearchConfig) : MetaM Index := do
  return tacticsIndex.merge (← backwardIndex config.localTheoremRules)
    |>.merge (← localTheoremIndex config.localTheoremRules)

end Bubble
