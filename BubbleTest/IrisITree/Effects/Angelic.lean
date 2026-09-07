module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Angelic
public import BubbleTest.IrisITree.Core.Wpi

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree IrisITree.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def angelicH (α : Type _) : IHandler PROP (angelicE α) where
  ihandle := λ _ Φ _ => iprop(∃ a, Φ a)
  ihandle_mono := by
    ibubble
    -- iintro %p %Φ %Φ' %s %s' HΦwand #Hswand H
    -- icases H with ⟨%a, HΦ⟩
    -- iexists a; iapply HΦwand $$ HΦ

instance angelicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (angelicH (PROP := PROP) α) := by
  constructor
  unfold angelicH
  ibubble
  -- iintro %p %Φ %s H
  -- iexact H

end handler

section wpi_rules

open ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : angelicE α -< E] [Hin : InH (angelicH (PROP := PROP) α) H]

attribute [local ibubble backward 75%] wpi_trigger
attribute [local ibubble backward 50%] fupd_mask_intro
attribute [local simp] angelicH

theorem wpi_angelic (M : CoPset) (p : α → Prop) (a : {x // p x}) (Ψ : {x // p x} → PROP) :
    Ψ a ⊢ (WPi (choose_angelic p) @> H; M {{ Ψ }}) := by
  unfold choose_angelic
  ibubble pureBy simp
  -- iintro HΨ
  -- iapply wpi_trigger; simp [angelicH]
  -- iapply fupd_mask_intro
  -- · simp
  -- iintro Hfalse; iexists a
  -- imod Hfalse; imodintro; iexact HΨ

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

attribute [local simp] angelicH
attribute [local simp] angelicEH

instance angelicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (angelicH (PROP := PROP) α) (angelicEH α) where
  inv _ := iprop(emp)
  adequate := by
    ibubble pureBy simp_all
    -- intro i s C Φ1 Φ2 Hhandle
    -- simp [angelicH, angelicEH] at Hhandle ⊢
    -- iexists a, s
    -- iframe
    -- itrivial

end exec
