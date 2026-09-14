module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Halt
public import BubbleTest.IrisITreeScript.Core.Wpi

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree IrisITreeScript.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def haltH : IHandler PROP haltE where
  ihandle := λ _ _ _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro H0_1
    iintro H0_2
    iintro H0_3
    icases H0_2 with #H0_4
    iexact H0_3

instance haltH_sequential : Sequential (PROP := PROP) haltH := by
  constructor
  unfold haltH
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  simp_all only
  iexact H0_1

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]  {E : Effect}
  {H : IHandler PROP E} [sub: haltE -< E] [Hin : InH haltH H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] haltH

@[ibubble 75%]
theorem wpi_halt {R} (Φ : R → PROP) :
    ⊢ WPi halt @> H; ⊤ {{ Φ }} := by
  unfold halt
  simp_all only [haltH]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Core.wpi_trigger
  simp_all only
  iapply Iris.fupd_mask_intro
  simp
  iintro H3_1
  imod H3_1 with H3_1
  icases H3_1 with #H4_1
  (ipureintro; simp)

theorem wpi_assume [BIAffine PROP] (P : Prop) [Decidable P] (Φ : { _x // P } → PROP) :
    (∀ HP, Φ HP) ⊢ WPi HaltE.assume P @> H; ⊤ {{ Φ }} := by
  unfold HaltE.assume; by_cases HP : P
  · iintro H0_1
    simp_all only
    simp_all only [haltH, ↓reduceDIte]
    iapply IrisITreeScript.Core.wpi_pure
    iexact H0_1
  · iintro H0_1
    simp_all only
    simp_all only [haltH, ↓reduceDIte]
    iapply IrisITreeScript.Effects.wpi_halt

end wpi_rules

section exec

open ITree.Exec ITree.Effects IrisITreeScript.Core

instance haltEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (haltH (PROP := PROP)) haltEH where
  inv _ := iprop(True)
  adequate := by
    intro i s C Φ1 Φ2 Hhandle
    cases Hhandle

end exec
