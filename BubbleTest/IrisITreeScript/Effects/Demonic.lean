module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Demonic
public import BubbleTest.IrisITreeScript.Core.Wpi

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree IrisITreeScript.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def demonicH (α : Type _) : IHandler PROP (demonicE α) where
  ihandle := λ _ Φ _ => iprop(∀ a, Φ a)
  ihandle_mono := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro H0_1
    iintro H0_2
    iintro H0_3
    iintro %a
    icases H0_2 with #H0_4
    iapply H0_1
    iexact H0_3

instance demonicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) α) := by
  constructor
  unfold demonicH
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  simp_all only
  iintro %a
  iexact H0_1

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} {α : Type _}
  [sub : demonicE α -< E] [Hin : InH (demonicH (PROP := PROP) α) H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] demonicH

theorem wpi_demonic (M : CoPset) (Φ : α → Prop) [Hdec : DecidablePred Φ]
    [Hi: Inhabited {a // Φ a}] (Ψ : {a // Φ a} → PROP) :
    (∀ a, Ψ a) ⊢ WPi choose Φ @> H;M {{ Ψ }} := by
  unfold choose
  iintro H0_1
  simp_all only [demonicH]
  iapply IrisITreeScript.Core.wpi_trigger
  simp_all only
  iapply Iris.fupd_mask_intro
  simp
  iintro H2_1
  iintro %a
  imod H2_1 with H2_1
  icases H2_1 with #H3_1
  imodintro
  iexact H0_1

end wpi_rules

section exec

open ITree.Exec IrisITreeScript.Core

attribute [local simp] demonicH demonicEH

instance demonicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (demonicH (PROP := PROP) α) (demonicEH α) where
  inv _ := iprop(emp)
  adequate := by
    intro i s C Φ1 Φ2 ⟨a, s', HC⟩
    iintro H0_1
    iintro H0_2
    icases H0_2 with #H0_3
    simp_all only [demonicH]
    iexists _
    iexists _
    imodintro
    isplit
    ipureintro
    pick_goal 4
    isplit
    ipureintro
    pick_goal 2
    iexact H0_1
    pick_goal 7
    pick_goal 7
    pick_goal 7
    pick_goal 7
    pick_goal 6
    pick_goal 7
    all_goals try simp
    exact HC

end exec
