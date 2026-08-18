module

public meta import Std.Data.TreeMap
public meta import Bubble.Core.Meta
public meta import Bubble.Core.Accessors

public meta section

open Lean Lean.Meta

namespace Bubble

abbrev BubbleTree := Std.TreeMap BubbleId Bubble compare
abbrev RappTree := Std.TreeMap RappId RappRef compare
abbrev GoalTree := Std.TreeMap GoalId GoalRef compare

/--
  Runtime arena for speculative nodes, fresh identifiers, and the replay
  certificate selected by search. The graph edges remain in Goal/Rapp/Plat.
-/
structure SearchStore where
  root : PlatRef
  nextGoalId : GoalId
  nextRappId : RappId
  nextPlatId : PlatId
  nextBubbleId : BubbleId
  nextGroupId : GroupId
  result? : Option BubbleId

  /- Fast & stable index from bubbleId, rappId, and goalId to its corresponding entity. -/
  bubbles : BubbleTree
  rapps : RappTree
  goals : GoalTree

/--
  Construct an initial store for our search procedure.
-/
def mkInitialStore (root : MVarId) : Lean.Elab.Tactic.TacticM SearchStore := do
  let goalType ← root.withContext do
    instantiateMVars (← root.getType)
  let some _ := Iris.ProofMode.parseIrisGoal? goalType
    | throwError "ibubble: root goal is not an Iris proof-mode goal"

  let rootState ← liftM (m := MetaM) saveState
  let rootGroup : Group := {
    id := .zero
    goals := #[.zero]
    link? := none
  }
  let rootPlatRef ← IO.mkRef <| Plat.mk {
    id := .zero
    parent? := none
    goals := #[]
    groups := #[rootGroup]
    join := { roots := #[.zero] }
    kind := .single
    bubbleToGroup := {}
  }
  let rootGoalRef ← IO.mkRef <| Goal.mk {
    id := .zero
    parent := rootPlatRef
    children := #[]
    depth := 0
    slot := 0
    isForcedUnprovable := false
    preNormGoal := root
    preNormState := rootState
    normalizationState := .notNormal
    unassignedMvars := ← root.withContext root.getMVarDependencies
    successProbability := .hundred
    addedInIteration := 1
    lastExpandedInIteration := 1
    rulesQueue? := none
    appendiedGoalId := #[]
  }

  rootPlatRef.modify λ plat => plat.setGoals #[rootGoalRef]
  return {
    root := rootPlatRef
    bubbles := Std.TreeMap.empty
    rapps := Std.TreeMap.empty
    goals := (Std.TreeMap.empty : GoalTree).insert .zero rootGoalRef
    result? := none
    nextGoalId := .one
    nextRappId := .zero
    nextPlatId := .one
    nextBubbleId := .zero
    nextGroupId := .one
  }

namespace TreeM

structure Context where
  currentIteration : Iteration := 1
  deriving Inhabited

end TreeM

/--
  Search-tree state over Lean's tactic monad.
  Goal scheduling remains owned by SearchM
-/
abbrev TreeM := ReaderT TreeM.Context <|
  StateRefT SearchStore Lean.Elab.Tactic.TacticM

namespace TreeM

instance : Inhabited (TreeM α) where
  default := failure

def run (ctx : Context) (store : SearchStore) (action : TreeM α) :
    Lean.Elab.Tactic.TacticM (α × SearchStore) :=
  ReaderT.run action ctx |>.run store

def getRootPlat : TreeM PlatRef :=
  return (← get).root

def getRootGoals : TreeM (Array GoalRef) := do
  return (← (← getRootPlat).get).goals

def getRootGoal : TreeM GoalRef := do
  let goals ← getRootGoals
  if h : goals.size = 1 then
    return goals[0]
  else
    throwError "ibubble: expected exactly one root goal, found {goals.size}"

def getRootMVar : TreeM MVarId := do
  return (← (← getRootGoal).get).preNormGoal

def getResult? : TreeM (Option BubbleId) :=
  return (← get).result?

def setResult (bubbleId : BubbleId) : TreeM Unit :=
  modifyThe SearchStore fun store => { store with result? := some bubbleId }

def getBubble? (bubbleId : BubbleId) : TreeM (Option Bubble) :=
  return (← get).bubbles.get? bubbleId

def getRapp? (rappId : RappId) : TreeM (Option RappRef) :=
  return (← get).rapps.get? rappId

def getGoal? (goalId : GoalId) : TreeM (Option GoalRef) :=
  return (← get).goals.get? goalId

def addBubble (bubble : Bubble) : TreeM Unit := do
  let store ← get
  if store.bubbles.get? bubble.id |>.isSome then
    throwError "ibubble: bubble ID {bubble.id} is already registered"
  modifyThe SearchStore fun store => {
    store with bubbles := store.bubbles.insert bubble.id bubble
  }

def addRapp (rappRef : RappRef) : TreeM Unit := do
  let rapp ← rappRef.get
  let store ← get
  if store.rapps.get? rapp.id |>.isSome then
    throwError "ibubble: Rapp ID {rapp.id} is already registered"
  modifyThe SearchStore fun store => {
    store with rapps := store.rapps.insert rapp.id rappRef
  }

def addGoal (goalRef : GoalRef) : TreeM Unit := do
  let goal ← goalRef.get
  let store ← get
  if store.goals.get? goal.id |>.isSome then
    throwError "ibubble: goal ID {goal.id} is already registered"
  modifyThe SearchStore fun store => {
    store with goals := store.goals.insert goal.id goalRef
  }

def getAndIncrementNextGoalId : TreeM GoalId := do
  modifyGetThe SearchStore fun store =>
    let id := store.nextGoalId
    (id, { store with nextGoalId := id.succ })

def getAndIncrementNextRappId : TreeM RappId := do
  modifyGetThe SearchStore fun store =>
    let id := store.nextRappId
    (id, { store with nextRappId := id.succ })

def getAndIncrementNextPlatId : TreeM PlatId := do
  modifyGetThe SearchStore fun store =>
    let id := store.nextPlatId
    (id, { store with nextPlatId := id.succ })

def getAndIncrementNextBubbleId : TreeM BubbleId := do
  modifyGetThe SearchStore fun store =>
    let id := store.nextBubbleId
    (id, { store with nextBubbleId := id.succ })

def getAndIncrementNextGroupId : TreeM GroupId := do
  modifyGetThe SearchStore fun store =>
    let id := store.nextGroupId
    (id, { store with nextGroupId := id.succ })

end TreeM

end Bubble
