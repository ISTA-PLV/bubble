module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Angelic
public import BubbleTest.IrisITreeScript.Core.Wpi

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree IrisITreeScript.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def angelicH (α : Type _) : IHandler PROP (angelicE α) where
  ihandle := λ _ Φ _ => iprop(∃ a, Φ a)
  ihandle_mono := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro H0_1
    iintro H0_2
    iintro H0_3
    icases H0_3 with ⟨%h0_1, H0_4⟩
    icases H0_2 with #H0_5
    iexists _
    iapply H0_1
    iexact H0_4

instance angelicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (angelicH (PROP := PROP) α) := by
  constructor
  unfold angelicH
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  icases H0_1 with ⟨%h0_1, H0_2⟩
  simp_all only
  iexists _
  iexact H0_2

end handler

section wpi_rules

open ITree

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : angelicE α -< E] [Hin : InH (angelicH (PROP := PROP) α) H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] angelicH

theorem wpi_angelic (M : CoPset) (p : α → Prop) (a : {x // p x}) (Ψ : {x // p x} → PROP) :
    Ψ a ⊢ (WPi (choose_angelic p) @> H; M {{ Ψ }}) := by
  unfold choose_angelic
  iintro H0_1
  simp_all only [angelicH]
  iapply IrisITreeScript.Core.wpi_trigger
  simp_all only
  iexists _
  iapply Iris.fupd_mask_intro
  simp
  iintro H3_1
  imod H3_1 with H3_1
  icases H3_1 with #H4_1
  imodintro
  iexact H0_1

end wpi_rules

section exec

open ITree.Exec IrisITreeScript.Core

attribute [local simp] angelicH
attribute [local simp] angelicEH

instance angelicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (angelicH (PROP := PROP) α) (angelicEH α) where
  inv _ := iprop(emp)
  adequate := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro %h0_5
    iintro H0_1
    iintro H0_2
    icases H0_2 with #H0_3
    simp_all only [angelicEH, angelicH]
    icases H0_1 with ⟨%h0_1, H0_4⟩
    iexists _
    iexists _
    assumption
    imodintro
    isplit
    (ipureintro; simp_all)
    isplit
    (ipureintro; simp_all)
    iexact H0_4

end exec
