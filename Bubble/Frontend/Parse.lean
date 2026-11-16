-- SPDX-License-Identifier: Apache-2.0
module

public meta import Iris.ProofMode.Tactics.Basic
public meta import Bubble.Frontend.Basic
public meta import Bubble.Search.Configure

public meta section

namespace Bubble

open Lean Elab Tactic

private meta def parseNormMode (stx : Syntax) : TermElabM Bool := do
  match stx with
  | `(ibubbleNormMode| simp) => pure true
  | `(ibubbleNormMode| noSimp) => pure false
  | _ => throwUnsupportedSyntax

private meta def parseStrategy (stx : Syntax) : TermElabM Strategy := do
  match stx with
  | `(ibubbleStrategy| bestFirst) => pure .bestFirst
  | `(ibubbleStrategy| depthFirst) => pure .depthFirst
  | `(ibubbleStrategy| breadthFirst) => pure .breadthFirst
  | _ => throwUnsupportedSyntax

private meta def parsePureSolver (stx : Syntax) : TermElabM (Bool × Syntax) := do
  match stx with
  | `(ibubblePureSolver| pureBy $solver:tactic) => pure (false, solver.raw)
  | `(ibubblePureSolver| pureStop) => pure (true, defaultPureSolver)
  | _ => throwUnsupportedSyntax

private meta def parseTheoremLimit (stx : Syntax) : TermElabM Nat := do
  match stx with
  | `(ibubbleTheoremLimit| maxTheoremUses $limit:num) =>
      let some limit := limit.raw.isNatLit?
        | throwError "ibubble: expected a numeral theorem-use limit"
      if limit == 0 then
        throwError "ibubble: maxTheoremUses must be positive"
      return limit
  | _ => throwUnsupportedSyntax

private meta def parseDepthLimit (stx : Syntax) : TermElabM Nat := do
  match stx with
  | `(ibubbleDepthLimit| maxDepth $limit:num) =>
      let some limit := limit.raw.isNatLit?
        | throwError "ibubble: expected a numeral search-depth limit"
      if limit == 0 then
        throwError "ibubble: maxDepth must be positive"
      return limit
  | _ => throwUnsupportedSyntax

private meta def parseSuccessProbability (p : Syntax) : TermElabM Percent := do
  let some p := p.isNatLit?
    | throwError "ibubble: expected a numeral success probability for local rule"
  match Percent.ofNat p with
  | some p => return p
  | none => throwError
      "ibubble: local rule success probability '{p}%' is not between 0 and 100"

private meta def parseRuleDecl (declStx : Syntax) : TermElabM Name := do
  Lean.Elab.realizeGlobalConstNoOverloadWithInfo declStx

private meta def parseRuleDirection (stx : Syntax) : TermElabM RuleDirection := do
  match stx with
  | `(ibubbleRuleDirection| backward) => pure .backward
  | `(ibubbleRuleDirection| forward) => pure .forward
  | _ => throwUnsupportedSyntax

private meta def parseLocalRule (stx : Syntax) : TermElabM LocalTheoremRule := do
  match stx with
  | `(ibubbleLocalRule| $declStx:ident) =>
      return {
        direction := .backward
        decl := ← parseRuleDecl declStx
        action := .insert .hundred
      }
  | `(ibubbleLocalRule| $declStx:ident $p:num %) =>
      return {
        direction := .backward
        decl := ← parseRuleDecl declStx
        action := .insert (← parseSuccessProbability p)
      }
  | `(ibubbleLocalRule| $dir:ibubbleRuleDirection $declStx:ident) =>
      return {
        direction := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        action := .insert .hundred
      }
  | `(ibubbleLocalRule| $dir:ibubbleRuleDirection $declStx:ident $p:num %) =>
      return {
        direction := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        action := .insert (← parseSuccessProbability p)
      }
  | _ => throwUnsupportedSyntax

private meta def parseErasedRule (stx : Syntax) : TermElabM LocalTheoremRule := do
  match stx with
  | `(ibubbleErasedRule| $declStx:ident) =>
      return {
        direction := .backward
        decl := ← parseRuleDecl declStx
        action := .erase
      }
  | `(ibubbleErasedRule| $dir:ibubbleRuleDirection $declStx:ident) =>
      return {
        direction := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        action := .erase
      }
  | _ => throwUnsupportedSyntax

private meta def parseRuleEdit (stx : Syntax) : TermElabM (Array LocalTheoremRule) := do
  match stx with
  | `(ibubbleRuleEdit| with [$[$rules:ibubbleLocalRule],*]) =>
      rules.mapM parseLocalRule
  | `(ibubbleRuleEdit| without [$[$rules:ibubbleErasedRule],*]) =>
      rules.mapM parseErasedRule
  | _ => throwUnsupportedSyntax

private meta def parseRuleEdits (edits : Array (TSyntax `ibubbleRuleEdit)) :
    TermElabM (Array LocalTheoremRule) := do
  let mut localTheoremRules := #[]
  for edit in edits do
    localTheoremRules := localTheoremRules ++ (← parseRuleEdit edit)
  return localTheoremRules

private meta def mkConfig (generateScript? : Bool)
    (strategyStx? : Option (TSyntax `ibubbleStrategy))
    (normModeStx? : Option (TSyntax `ibubbleNormMode))
    (pureSolverStx? : Option (TSyntax `ibubblePureSolver))
    (theoremLimitStx? : Option (TSyntax `ibubbleTheoremLimit))
    (depthLimitStx? : Option (TSyntax `ibubbleDepthLimit))
    (ruleEdits : Array (TSyntax `ibubbleRuleEdit)) : TermElabM SearchConfig := do
  let strategy ← match strategyStx? with
    | none => pure .bestFirst
    | some strategyStx => parseStrategy strategyStx
  let enableSimp? ← match normModeStx? with
    | none => pure ({} : SearchConfig).enableSimp?
    | some normModeStx => parseNormMode normModeStx
  let (pureStop?, pureSolver) ← match pureSolverStx? with
    | none => pure (false, defaultPureSolver)
    | some pureSolverStx => parsePureSolver pureSolverStx
  let theoremUseLimit ← match theoremLimitStx? with
    | none => pure defaultMaxTheoremUses
    | some theoremLimitStx => parseTheoremLimit theoremLimitStx
  let depthLimit ← match depthLimitStx? with
    | none => pure ({} : SearchConfig).maxDepth
    | some depthLimitStx => parseDepthLimit depthLimitStx
  let localTheoremRules ← parseRuleEdits ruleEdits
  return {
    generateScript?
    strategy
    enableSimp?
    pureSolver
    pureStop?
    «maxTheoremUses» := theoremUseLimit
    «maxDepth» := depthLimit
    localTheoremRules
  }

/- Parse given syntax into search configuration -/
meta def parse (stx : Syntax) : TermElabM SearchConfig := do
  withRef stx do
    match stx with
    | `(tactic| ibubble $[$strategy:ibubbleStrategy]? $[$normMode:ibubbleNormMode]?
        $[$pureSolver:ibubblePureSolver]?
        $[$theoremLimit:ibubbleTheoremLimit]?
        $[$depthLimit:ibubbleDepthLimit]?
        $[$ruleEdits:ibubbleRuleEdit]*) =>
        mkConfig false strategy normMode pureSolver theoremLimit depthLimit ruleEdits
    | `(tactic| ibubble? $[$strategy:ibubbleStrategy]? $[$normMode:ibubbleNormMode]?
        $[$pureSolver:ibubblePureSolver]?
        $[$theoremLimit:ibubbleTheoremLimit]?
        $[$depthLimit:ibubbleDepthLimit]?
        $[$ruleEdits:ibubbleRuleEdit]*) =>
        mkConfig true strategy normMode pureSolver theoremLimit depthLimit ruleEdits
    | _ =>
        throwUnsupportedSyntax

end Bubble
