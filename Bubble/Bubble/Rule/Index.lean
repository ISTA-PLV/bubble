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

/--
  Lower a registered theorem into rules of the given direction. A backward
  bi-entailment is split into two explicitly oriented rules; forward rules act on
  hypotheses rather than the target, so they are left unindexed.
-/
private def theoremRules (scope : RuleScope) (direction : RuleDirection)
    (decl : Name) (probability : Percent) : MetaM (Array Rule) := do
  if direction == .forward then
    return #[theoremRule scope direction decl probability]
  let info ← getConstInfo decl
  let (_, _, body) ← forallMetaTelescopeReducing info.type
  let body ← whnf body
  let some args := body.appM? ``BIBase.BiEntails
    | return #[theoremRule scope direction decl probability]
  let some lhs := args[args.size - 2]? | return #[]
  let some rhs := args[args.size - 1]? | return #[]
  let mpMode ← IndexingMode.targetMatching rhs
  let mprMode ← IndexingMode.targetMatching lhs
  return #[
    theoremRule scope direction decl probability .mp mpMode,
    theoremRule scope direction decl probability .mpr mprMode
  ]

/--
  Rules registered with `@[ibubble]`. A theorem mentioned by a local rule edit in
  the same direction (`with` or `without`) is left out, so the local edit wins.
-/
private def globalIndex (localRules : Array LocalTheoremRule) : MetaM Index := do
  let registered := [
    (RuleDirection.backward, ← getIbubbleBackwardLemmas),
    (RuleDirection.forward, ← getIbubbleForwardLemmas)
  ]
  let mut index : Index := {}
  for (direction, entries) in registered do
    for entry in entries do
      if localRules.any λ rule => rule.direction == direction && rule.decl == entry.decl then
        continue
      for rule in ← theoremRules .global direction entry.decl entry.successProbability do
        index := index.add rule rule.indexingMode
  return index

/--
  Rules added for a single `ibubble` invocation with `with [...]`. `without [...]`
  takes priority: a theorem erased in the same direction is not added.
-/
private def localIndex (localRules : Array LocalTheoremRule) : MetaM Index := do
  let mut index : Index := {}
  for localRule in localRules do
    let .insert probability := localRule.action | continue
    let erased := localRules.any λ rule =>
      rule.action matches .erase &&
        rule.direction == localRule.direction && rule.decl == localRule.decl
    if erased then continue
    for rule in ← theoremRules .local localRule.direction localRule.decl probability do
      index := index.add rule rule.indexingMode
  return index

/-- Return back all potential rules' set in `Bubble`. -/
def buildIndex (config : SearchConfig) : MetaM Index := do
  return tacticsIndex.merge (← globalIndex config.localTheoremRules)
    |>.merge (← localIndex config.localTheoremRules)

end Bubble
