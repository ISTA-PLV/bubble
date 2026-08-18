module

public meta import Batteries.Data.BinomialHeap.Basic
public meta import Bubble.Core.Accessors
public meta import Bubble.Search.Configure

public meta section

namespace Bubble.Search

open Batteries (BinomialHeap)

class Queue (Q : Type) where
  empty : BaseIO Q
  insert : Q → Array GoalRef → BaseIO Q
  pop? : Q → BaseIO (Option GoalRef × Q)
  toArray : Q → BaseIO (Array GoalRef)

namespace Queue

def ofArray [Queue Q] (goals : Array GoalRef) : BaseIO Q := do
  Queue.insert (← Queue.empty) goals

end Queue

namespace BestFirstQueue

structure Entry where
  goal : GoalRef
  priority : Percent
  lastExpanded : Iteration
  added : Iteration

protected def Entry.le (left right : Entry) : Bool :=
  left.priority > right.priority ||
    (left.priority == right.priority &&
      (left.lastExpanded < right.lastExpanded ||
        (left.lastExpanded == right.lastExpanded && left.added ≤ right.added)))

def Entry.ofGoal (goalRef : GoalRef) : BaseIO Entry := do
  let goal ← goalRef.get
  return {
    goal := goalRef
    priority := goal.successProbability
    lastExpanded := goal.lastExpandedInIteration
    added := goal.addedInIteration
  }

end BestFirstQueue

abbrev BestFirstQueue :=
  BinomialHeap BestFirstQueue.Entry BestFirstQueue.Entry.le

meta instance : Queue BestFirstQueue where
  empty := pure BinomialHeap.empty
  insert queue goals := goals.foldlM (init := queue) fun queue goal => do
    return BinomialHeap.insert (← BestFirstQueue.Entry.ofGoal goal) queue
  pop? queue := pure <| match queue.deleteMin with
    | none => (none, queue)
    | some (entry, queue) => (some entry.goal, queue)
  toArray queue := pure <| queue.toArray.map (·.goal)

structure LIFOQueue where
  goals : Array GoalRef := #[]

meta instance : Queue LIFOQueue where
  empty := pure {}
  insert queue goals := pure { goals := queue.goals ++ goals.reverse }
  pop? queue := pure <| match queue.goals.back? with
    | none => (none, queue)
    | some goal => (some goal, { goals := queue.goals.pop })
  toArray queue := pure queue.goals

structure FIFOQueue where
  goals : Array GoalRef := #[]
  position : Nat := 0

meta instance : Queue FIFOQueue where
  empty := pure {}
  insert queue goals := pure { queue with goals := queue.goals ++ goals }
  pop? queue := pure <| if h : queue.position < queue.goals.size then
    (some queue.goals[queue.position], { queue with position := queue.position + 1 })
  else
    (none, queue)
  toArray queue := pure <| queue.goals.extract queue.position queue.goals.size

namespace Queue

meta def withStrategy {m : Type → Type} (strategy : Strategy)
    (k : (Q : Type) → [Queue Q] → m α) : m α :=
  match strategy with
  | .bestFirst => k BestFirstQueue
  | .depthFirst => k LIFOQueue
  | .breadthFirst => k FIFOQueue

end Queue

end Bubble.Search
