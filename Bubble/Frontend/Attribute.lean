module

public meta import Lean
public meta import Bubble.Util.Percent

public meta section

namespace Bubble

open Lean Elab

structure RuleAttrEntry where
  decl : Name
  successProbability : Percent
  deriving Inhabited

/-- Theorems registered with `@[ibubble backward <p>%]`. -/
initialize ibubbleBackwardExt :
    SimpleScopedEnvExtension RuleAttrEntry (Array RuleAttrEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s entry =>
      (s.filter fun old => old.decl != entry.decl).push entry
    initial := #[]
  }

/-- Theorems registered with `@[ibubble forward <p>%]`. -/
initialize ibubbleForwardExt :
    SimpleScopedEnvExtension RuleAttrEntry (Array RuleAttrEntry) ←
  registerSimpleScopedEnvExtension {
    addEntry := λ s entry =>
      (s.filter fun old => old.decl != entry.decl).push entry
    initial := #[]
  }

namespace Parser

declare_syntax_cat ibubbleAttrRule
syntax "forward" num "%" : ibubbleAttrRule
syntax "backward" num "%" : ibubbleAttrRule
syntax num "%" : ibubbleAttrRule

syntax (name := ibubble) "ibubble" (ppSpace ibubbleAttrRule)+ : attr

end Parser

inductive AttrRule where
  | backward (successProbability : Percent)
  | forward (successProbability : Percent)

namespace AttrRule

private def elabSuccessProbability (kind : String) (p : Syntax) : CoreM Percent := do
  let some p := p.isNatLit?
    | throwError "ibubble: expected a numeral success probability for {kind} rule"
  match Percent.ofNat p with
  | some p => return p
  | none => throwError
      "ibubble: {kind} rule success probability '{p}%' is not between 0 and 100"

def «elab» (stx : Syntax) : CoreM AttrRule :=
  withRef stx do
    match stx with
    | `(ibubbleAttrRule| forward $p:num %) =>
      return .forward (← elabSuccessProbability "forward" p)
    | `(ibubbleAttrRule| backward $p:num %) =>
      return .backward (← elabSuccessProbability "backward" p)
    | `(ibubbleAttrRule| $p:num %) =>
      return .backward (← elabSuccessProbability "backward" p)
    | _ => throwUnsupportedSyntax

end AttrRule

structure AttrConfig where
  rules : Array AttrRule

namespace AttrConfig

def «elab» (stx : Syntax) : CoreM AttrConfig :=
  withRef stx do
    match stx with
    | `(attr| ibubble $[$rules:ibubbleAttrRule]*) =>
        return { rules := ← rules.mapM AttrRule.elab }
    | _ => throwUnsupportedSyntax

end AttrConfig

private def addBackwardRule (decl : Name) (successProbability : Percent)
    (kind : AttributeKind) : CoreM Unit := do
  if kind != .local && (ibubbleBackwardExt.getState (← getEnv)).any λ entry => entry.decl == decl then
    throwError "ibubble: backward rule '{decl}' is already registered"
  ibubbleBackwardExt.add { decl, successProbability } kind

private def addForwardRule (decl : Name) (successProbability : Percent)
    (kind : AttributeKind) : CoreM Unit := do
  if kind != .local && (ibubbleForwardExt.getState (← getEnv)).any λ entry => entry.decl == decl then
    throwError "ibubble: forward rule '{decl}' is already registered"
  ibubbleForwardExt.add { decl, successProbability } kind

initialize registerBuiltinAttribute {
  name := `ibubble
  descr := "Register a declaration as an ibubble rule."
  applicationTime := .afterCompilation
  add := fun decl stx kind => withRef stx do
    let config ← AttrConfig.elab stx
    for rule in config.rules do
      match rule with
      | .backward successProbability => addBackwardRule decl successProbability kind
      | .forward successProbability => addForwardRule decl successProbability kind
}

/-- All lemmas currently registered with `@[ibubble backward <p>%]`. -/
def getIbubbleBackwardLemmas [Monad m] [MonadEnv m] : m (Array RuleAttrEntry) := do
  return ibubbleBackwardExt.getState (← getEnv)

/-- All lemmas currently registered with `@[ibubble forward <p>%]`. -/
def getIbubbleForwardLemmas [Monad m] [MonadEnv m] : m (Array RuleAttrEntry) := do
  return ibubbleForwardExt.getState (← getEnv)

end Bubble
