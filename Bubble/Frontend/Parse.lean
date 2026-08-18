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

private meta def parseSuccessProbability (p : Syntax) : TermElabM Percent := do
  let some p := p.isNatLit?
    | throwError "ibubble: expected a numeral success probability for local rule"
  match Percent.ofNat p with
  | some p => return p
  | none => throwError
      "ibubble: local rule success probability '{p}%' is not between 0 and 100"

private meta def parseRuleDecl (declStx : Syntax) : TermElabM Name := do
  Lean.Elab.realizeGlobalConstNoOverloadWithInfo declStx

private meta def parseRuleDirection (stx : Syntax) : TermElabM RuleBuilderKind := do
  match stx with
  | `(ibubbleRuleDirection| backward) => pure .backward
  | `(ibubbleRuleDirection| forward) => pure .forward
  | _ => throwUnsupportedSyntax

private meta def parseLocalRule (stx : Syntax) : TermElabM LocalTheoremRule := do
  match stx with
  | `(ibubbleLocalRule| $dir:ibubbleRuleDirection $declStx:ident) =>
      return {
        kind := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        action := .insert .hundred
      }
  | `(ibubbleLocalRule| $dir:ibubbleRuleDirection $declStx:ident $p:num %) =>
      return {
        kind := ← parseRuleDirection dir
        decl := ← parseRuleDecl declStx
        action := .insert (← parseSuccessProbability p)
      }
  | _ => throwUnsupportedSyntax

private meta def parseErasedRule (stx : Syntax) : TermElabM LocalTheoremRule := do
  match stx with
  | `(ibubbleErasedRule| $dir:ibubbleRuleDirection $declStx:ident) =>
      return {
        kind := ← parseRuleDirection dir
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
    (ruleEdits : Array (TSyntax `ibubbleRuleEdit)) : TermElabM SearchConfig := do
  let strategy ← match strategyStx? with
    | none => pure .bestFirst
    | some strategyStx => parseStrategy strategyStx
  let enableSimp? ← match normModeStx? with
    | none => pure false
    | some normModeStx => parseNormMode normModeStx
  let (pureStop?, pureSolver) ← match pureSolverStx? with
    | none => pure (false, defaultPureSolver)
    | some pureSolverStx => parsePureSolver pureSolverStx
  let localTheoremRules ← parseRuleEdits ruleEdits
  return {
    generateScript?
    strategy
    enableSimp?
    pureSolver
    pureStop?
    localTheoremRules
  }

/- Parse given syntax into search configuration -/
meta def parse (stx : Syntax) : TermElabM SearchConfig := do
  withRef stx do
    match stx with
    | `(tactic| ibubble $[$strategy:ibubbleStrategy]? $[$normMode:ibubbleNormMode]?
        $[$pureSolver:ibubblePureSolver]?
        $[$ruleEdits:ibubbleRuleEdit]*) =>
        mkConfig false strategy normMode pureSolver ruleEdits
    | `(tactic| ibubble? $[$strategy:ibubbleStrategy]? $[$normMode:ibubbleNormMode]?
        $[$pureSolver:ibubblePureSolver]?
        $[$ruleEdits:ibubbleRuleEdit]*) =>
        mkConfig true strategy normMode pureSolver ruleEdits
    | _ =>
        throwUnsupportedSyntax

end Bubble
