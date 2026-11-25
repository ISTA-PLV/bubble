-- SPDX-License-Identifier: Apache-2.0
module

public import Bubble.Core.Data

public section

open Lean Lean.Meta Std

namespace Bubble

structure TreeSpec where
  Goal : Type
  Rapp : Type
  Plat : Type
  introGoal : GoalData (IO.Ref Rapp) (IO.Ref Plat) → Goal
  elimGoal : Goal → GoalData (IO.Ref Rapp) (IO.Ref Plat)
  introRapp : RappData (IO.Ref Goal) (IO.Ref Plat) → Rapp
  elimRapp : Rapp → RappData (IO.Ref Goal) (IO.Ref Plat)
  introPlat : PlatData (IO.Ref Goal) (IO.Ref Rapp) → Plat
  elimPlat : Plat → PlatData (IO.Ref Goal) (IO.Ref Rapp)

instance : Nonempty TreeSpec := by
  refine ⟨{
    Goal := Unit
    Rapp := Unit
    Plat := Unit
    introGoal := λ _ => ()
    elimGoal := λ _ => Classical.ofNonempty
    introRapp := λ _ => ()
    elimRapp := λ _ => Classical.ofNonempty
    introPlat := λ _ => ()
    elimPlat := λ _ => Classical.ofNonempty
  }⟩

mutual
  unsafe inductive GoalUnsafe where
    | mk : GoalData (IO.Ref RappUnsafe) (IO.Ref PlatUnsafe) → GoalUnsafe

  unsafe inductive RappUnsafe where
    | mk : RappData (IO.Ref GoalUnsafe) (IO.Ref PlatUnsafe) → RappUnsafe

  unsafe inductive PlatUnsafe where
    | mk : PlatData (IO.Ref GoalUnsafe) (IO.Ref RappUnsafe) → PlatUnsafe
end

unsafe def treeImpl : TreeSpec where
  Goal := GoalUnsafe
  Rapp := RappUnsafe
  Plat := PlatUnsafe
  introGoal := GoalUnsafe.mk
  elimGoal | GoalUnsafe.mk x => x
  introRapp := RappUnsafe.mk
  elimRapp | RappUnsafe.mk x => x
  introPlat := PlatUnsafe.mk
  elimPlat | PlatUnsafe.mk x => x

@[implemented_by treeImpl]
opaque tree : TreeSpec

public abbrev Goal := tree.Goal
public abbrev Rapp := tree.Rapp
public abbrev Plat := tree.Plat

public abbrev GoalRef   := IO.Ref Goal
public abbrev RappRef   := IO.Ref Rapp
public abbrev PlatRef   := IO.Ref Plat
public abbrev CtxSegRef := PlatRef

end Bubble
