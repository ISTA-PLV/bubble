-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.Types

public meta section

namespace Bubble

open Lean

structure GroupLink where
  predecessor : GroupId
  slot        : GoalSlot
  bubble      : BubbleId

structure Group where
  id    : GroupId
  goals : Array GoalId
  link? : Option GroupLink

namespace Group

private structure DependencyUnionFind where
  parents : Array Nat
  ranks : Array Nat

namespace DependencyUnionFind

/-- Create one singleton set for each goal. -/
private def init (size : Nat) : DependencyUnionFind := Id.run do
  let mut parents := Array.mkEmpty size
  for index in [:size] do
    parents := parents.push index
  return { parents, ranks := Array.replicate size 0 }

/-- Find a representative and compress the traversed parent path. -/
private partial def find (sets : DependencyUnionFind) (index : Nat) :
    Nat × DependencyUnionFind :=
  let parent := sets.parents[index]!
  if parent == index then
    (index, sets)
  else
    let (root, sets) := find sets parent
    (root, { sets with parents := sets.parents.set! index root })

/-- Merge two sets by rank. -/
private def union (sets : DependencyUnionFind) (left right : Nat) :
    DependencyUnionFind :=
  let (leftRoot, sets) := sets.find left
  let (rightRoot, sets) := sets.find right
  if leftRoot == rightRoot then sets
  else
    let leftRank := sets.ranks[leftRoot]!
    let rightRank := sets.ranks[rightRoot]!
    if leftRank < rightRank then
      { sets with parents := sets.parents.set! leftRoot rightRoot }
    else if rightRank < leftRank then
      { sets with parents := sets.parents.set! rightRoot leftRoot }
    else
      { parents := sets.parents.set! rightRoot leftRoot
        ranks := sets.ranks.set! leftRoot (leftRank + 1) }

end DependencyUnionFind

/-- Partition goals by the connected components of their shared metavariables. -/
def partitionDependencies
    (goals : Array (GoalId × Std.HashSet MVarId)) : Array (Array GoalId) := Id.run do
  let mut sets := DependencyUnionFind.init goals.size
  let mut firstGoalFor : Std.HashMap MVarId Nat := {}
  for index in [:goals.size] do
    for dependency in goals[index]!.2 do
      match firstGoalFor[dependency]? with
      | some first => sets := sets.union first index
      | none => firstGoalFor := firstGoalFor.insert dependency index

  let mut componentForRoot : Std.HashMap Nat Nat := {}
  let mut components : Array (Array GoalId) := #[]
  for index in [:goals.size] do
    let (root, compressed) := sets.find index
    sets := compressed
    match componentForRoot[root]? with
    | some component =>
        components := components.modify component fun members =>
          members.push goals[index]!.1
    | none =>
        componentForRoot := componentForRoot.insert root components.size
        components := components.push #[goals[index]!.1]
  return components

end Group

end Bubble
