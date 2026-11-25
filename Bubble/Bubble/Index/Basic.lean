-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Index.Types
public meta import Bubble.Rule.Types

public meta section

open Lean Lean.Meta

namespace Bubble

structure Index where
  byFullGoal : DiscrTree Rule
  byTarget : DiscrTree Rule
  byIrisHyp : DiscrTree Rule
  byLeanHyp : DiscrTree Rule
  unindexed : Std.HashSet Rule
  deriving Inhabited

namespace Index

instance : EmptyCollection Index where
  emptyCollection := {
    byFullGoal := {}
    byTarget := {}
    byIrisHyp := {}
    byLeanHyp := {}
    unindexed := {}
  }

def merge (rilhs rirhs : Index) : Index where
  byFullGoal := rilhs.byFullGoal.mergePreservingDuplicates rirhs.byFullGoal
  byTarget := rilhs.byTarget.mergePreservingDuplicates rirhs.byTarget
  byIrisHyp := rilhs.byIrisHyp.mergePreservingDuplicates rirhs.byIrisHyp
  byLeanHyp := rilhs.byLeanHyp.mergePreservingDuplicates rirhs.byLeanHyp
  unindexed := rilhs.unindexed.union rirhs.unindexed

partial def add (rule : Rule) (mode : IndexingMode) (idx : Index) :
    Index :=
  match mode with
  | .unindexed =>
    { idx with unindexed := idx.unindexed.insert rule }
  | .fullGoal keys =>
    { idx with byFullGoal := idx.byFullGoal.insertKeyValue keys rule }
  | .target keys =>
    { idx with byTarget := idx.byTarget.insertKeyValue keys rule }
  | .irisHyps keys =>
    { idx with byIrisHyp := idx.byIrisHyp.insertKeyValue keys rule }
  | .leanHyps keys =>
    { idx with byLeanHyp := idx.byLeanHyp.insertKeyValue keys rule }
  | .or modes =>
    modes.foldl (init := idx) λ idx mode => idx.add rule mode

end Index

end Bubble
