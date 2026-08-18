module

public meta import Batteries.Lean.Meta.SavedState
public meta import Bubble.Core.Types

public meta section

namespace Bubble.Meta

open Lean Lean.Meta Std

/-- Collect assignments made to the selected metavariables in a saved state. -/
def collectMetaInfo (mvars : HashSet MVarId) (state : SavedState) :
    MetaM (Array MetaAssignment) := do
  state.runMetaM' do
    mvars.toArray.foldlM (init := #[]) λ assignments mvarId => do
      let some value ← getExprMVarAssignment? mvarId | return assignments
      let value ← instantiateMVars value
      return assignments.push { mvarId, value, sourceState := state }

/-- Copy missing universe declarations and assignments from a branch state. -/
private def copyUniverseContext (source : SavedState) : MetaM Unit := do
  let sourceMCtx := source.meta.mctx
  modifyMCtx λ current =>
    let lDecls := sourceMCtx.lDecls.foldl (init := current.lDecls) λ decls id decl =>
      if decls.contains id then decls else decls.insert id decl
    let lAssignment := sourceMCtx.lAssignment.foldl
        (init := current.lAssignment) λ assignments id value =>
      if assignments.contains id then assignments else assignments.insert id value
    { current with
      lmvarCounter := max current.lmvarCounter sourceMCtx.lmvarCounter
      lDecls
      lAssignment }

/-- Copy one expression metavariable declaration and its dependency closure. -/
private partial def copyExprMVarDecl (source : SavedState) (mvarId : MVarId)
    (visited : HashSet MVarId := {}) : MetaM Unit := do
  if visited.contains mvarId then return
  let visited := visited.insert mvarId
  let (decl, dependencies) ← source.runMetaM' do
    let decl ← mvarId.getDecl
    let dependencies ← mvarId.getMVarDependencies (includeDelayed := true)
    return (decl, dependencies)
  copyUniverseContext source
  unless ← mvarId.isDeclared do
    modifyMCtx λ mctx => {
      mctx with
      mvarCounter := max mctx.mvarCounter source.meta.mctx.mvarCounter
      decls := mctx.decls.insert mvarId decl
    }
  dependencies.forM λ each => copyExprMVarDecl source each visited

/-- Import the declarations required to interpret a branch-local assignment. -/
private def prepareAssignment (assignment : MetaAssignment) : MetaM Unit := do
  copyUniverseContext assignment.sourceState
  let sourceMCtx := assignment.sourceState.meta.mctx
  modifyMCtx λ current =>
    let decls := sourceMCtx.decls.foldl (init := current.decls) λ decls id decl =>
      if decls.contains id then decls else decls.insert id decl
    { current with
      mvarCounter := max current.mvarCounter sourceMCtx.mvarCounter
      decls }
  for mvarId in ← getMVars assignment.value do
    copyExprMVarDecl assignment.sourceState mvarId

/-- Check whether two assignments for the same metavariable are compatible. -/
private def assignmentsCompatible (baseState : SavedState)
    (left right : MetaAssignment) : MetaM Bool :=
  baseState.runMetaM' do
    try
      prepareAssignment left
      prepareAssignment right
      isDefEq left.value right.value
    catch _ =>
      return false

/-- Merge compatible metavariable assignments collected from multiple branches. -/
def mergeMetaInfo (baseState : SavedState) (parts : Array (Array MetaAssignment)) :
    MetaM (Option (Array MetaAssignment)) := do
  parts.foldlM (init := some #[]) λ merged? part => do
    let some merged := merged? | return none
    part.foldlM (init := some merged) λ merged? assignment => do
      let some merged := merged? | return none
      match merged.find? (·.mvarId == assignment.mvarId) with
      | none => return some (merged.push assignment)
      | some old =>
          if ← assignmentsCompatible baseState old assignment then
            return some merged
          else return none

/-- Apply collected metavariable assignments to a copy of the given state. -/
def applyMetaInfo (baseState : SavedState) (metaInfo : Array MetaAssignment) :
    MetaM (Option SavedState) := do
  baseState.runMetaM' do
    try
      for assignment in metaInfo do
        copyExprMVarDecl assignment.sourceState assignment.mvarId
        prepareAssignment assignment
        if ← assignment.mvarId.isAssignedOrDelayedAssigned then
          unless ← isDefEq (mkMVar assignment.mvarId) assignment.value do
            return none
        else
          assignment.mvarId.assign assignment.value
      return some (← saveState)
    catch _ =>
      return none

/-- Apply rising assignments, hide Rapp-local metavariables, and re-extract outward assignments. -/
def propagateMetaInfo (baseState : SavedState) (rising : Array MetaAssignment)
    (introduced assigned : HashSet MVarId) : MetaM (Option (Array MetaAssignment)) := do
  let some refinedState ← applyMetaInfo baseState rising | return none
  let outward := rising.foldl (init := assigned) λ mvars assignment =>
    if introduced.contains assignment.mvarId then mvars
    else mvars.insert assignment.mvarId
  return some (← collectMetaInfo outward refinedState)

end Bubble.Meta
