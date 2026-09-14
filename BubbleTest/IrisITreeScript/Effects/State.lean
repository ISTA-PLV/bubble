module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITreeScript.Core.Wpi
public import ITree.Effects.State

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree ITree.Effects IrisITreeScript.Core

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def stateH {S : Type _} (stateInterp : S → PROP) : IHandler PROP (stateE S) where
  ihandle i Φ _ :=
    iprop(∀ s, stateInterp s ={∅}=∗ stateInterp (i s) ∗ Φ s)
  ihandle_mono := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro H0_1
    iintro H0_2
    iintro H0_3
    iintro %s
    iintro H0_4
    icases H0_2 with #H0_5
    ihave H0_6 := H0_3 $$ [ H0_4 ]
    iexact H0_4
    imod H0_6 with H0_6
    icases H0_6 with ⟨H2_1, H2_2⟩
    isplitl [H2_1]
    imodintro
    iexact H2_1
    iapply H0_1
    imodintro
    iexact H2_2

instance {S : Type _} (stateInterp : S → PROP) :
    Sequential (stateH stateInterp) := by
  constructor
  unfold stateH
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  simp_all only
  iintro %s
  iintro H0_2
  iapply H0_1
  iexact H0_2

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {S : Type _}
  (stateInterp : S → PROP)
  {E : Effect} {H : IHandler PROP E}
  [stateE S -< E] [Hin : InH (stateH stateInterp) H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] stateH

-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`.
theorem wpi_stateE_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi StateE.get @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.get StateE.modify
  iapply wpi_trigger; simp [stateH]
  iapply fupd_mask_intro (by simp); iintro >Hm
  iintro %x
  iintro H0_1
  icases Hm with #H0_2
  simp_all only [stateH]
  ihave H0_3 := Hw $$ [ H0_1 ]
  iexact H0_1
  imod H0_3 with H0_3
  icases H0_3 with ⟨H2_1, H2_2⟩
  iapply Iris.fupd_mask_intro
  simp
  iintro H3_1
  isplitl [H2_1]
  iexact H2_1
  imod H3_1 with H3_1
  icases H3_1 with #H5_1
  imodintro
  iexact H2_2

@[ibubble 75%]
theorem wpi_get Ms Me (Φ : S → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s ∗ Φ s) -∗
    WPi get @> H; Ms, Me {{Φ}} := wpi_stateE_get _ _ _ _

-- Allow a mask-changing fancy update from `Ms` to `Me` while handling `get`.
theorem wpi_stateE_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi StateE.set s' @> H; Ms, Me {{Φ}} := by
  iintro Hw; unfold StateE.set StateE.modify
  iapply wpi_trigger_bind
  simp_all only [stateH]
  iapply Iris.fupd_mask_intro
  simp
  iintro H1_1
  iintro %s
  iintro H1_2
  ihave H1_3 := Hw $$ [ H1_2 ]
  iexact H1_2
  imod H1_1 with H1_1
  icases H1_1 with #H3_1
  imod H1_3 with H1_3
  icases H1_3 with ⟨H4_1, H4_2⟩
  iapply Iris.fupd_mask_intro
  simp
  iintro H5_1
  isplitl [H4_1]
  iexact H4_1
  imod H5_1 with H5_1
  icases H5_1 with #H7_1
  iapply IrisITreeScript.Core.wpi_pure
  iexact H4_2

@[ibubble 75%]
theorem wpi_set Ms Me s' (Φ : PUnit → PROP) :
    (∀ s, stateInterp s ={Ms, Me}=∗ stateInterp s' ∗ Φ ⟨⟩) -∗
    WPi set s' @> H; Ms, Me {{Φ}} := wpi_stateE_set _ _ _ _ _

end wpi_rules

section exec

open ITree.Exec IrisITreeScript.Core

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {S : Type _} (stateInterp : S → PROP)

attribute [local simp] stateH stateEH

instance stateEH_adequate :
    SEHandlerAdequate (stateH stateInterp) (stateEH S) where
  inv s := stateInterp s
  adequate := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro %h0_5
    iintro H0_1
    iintro H0_2
    simp_all only [stateEH, stateH]
    iexists _
    iexists _
    isplitl []
    pick_goal 2
    iapply H0_1
    iexact H0_2
    simp_all only
    (ipureintro; simp)

end exec
