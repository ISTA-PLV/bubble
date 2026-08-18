module

public meta import Lean.Meta.Tactic.Rewrite
public meta import Bubble.Search.Normalization.Basic

public meta section

namespace Bubble.Search.Normalization

open Lean Lean.Meta Elab Tactic

private def mkRewriteTactic (hyp : Name) : MetaM (TSyntax `tactic) := do
  let hyp := mkIdent hyp
  `(tactic| rw [$hyp:term])

def rewriteStep : Step where
  label := "rewrite"
  run input := do
    input.goal.withContext do
      let target ← instantiateMVars (← input.goal.getType)
      for localDecl? in (← getLCtx).decls.toArray do
        let some localDecl := localDecl? | continue
        if localDecl.isImplementationDetail then continue
        let type ← instantiateMVars localDecl.type
        if (← matchEq? type).isNone then continue

        /- Attempt to do the rewrite operation. -/
        let result? ← tryAttempt do
          let result ← input.goal.rewrite target (.fvar localDecl.fvarId)
          if !result.mvarIds.isEmpty then return .unchanged
          let newGoal ← input.goal.replaceTargetEq result.eNew result.eqProof
          let tactic ← mkRewriteTactic localDecl.userName
          return .changed newGoal #[] (some tactic)
        if let some result := result? then return result
      return .unchanged

end Bubble.Search.Normalization
