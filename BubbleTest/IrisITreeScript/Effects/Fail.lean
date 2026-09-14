module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Fail
public import BubbleTest.IrisITreeScript.Core.Wpi

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree IrisITreeScript.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def failH : IHandler PROP failE where
  ihandle := λ _ _ _ => iprop(False)
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
    icases H0_3 with ⟨⟩

instance failH_sequential : Sequential (PROP := PROP) failH := by
  constructor
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  icases H0_1 with ⟨⟩

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] {E : Effect}
  {H : IHandler PROP E} [sub : failE -< E] [Hin : InH failH H]

theorem wpi_fail {R} (M : CoPset) (Φ : R → PROP) (s : String) :
    (WPi fail s @> H; M {{ Φ }}) ⊢ |={M}=> iprop(False) := by
  iintro Hwp; simp [fail, Effect.trigger]
  let e := @Subeffect.map failE E sub ({ down := s } : failE.I)
  ihave >Hwp := wpi_vis $$ Hwp
  have Hfalse : H.ihandle e.fst (fun _ => iprop(False)) (fun _ => iprop(False)) ⊢ iprop(False) :=
    (Hin.is_inH ({ down := s } : failE.I) (fun _ => iprop(False))
      (fun _ => iprop(False))).mpr.trans false_elim
  iapply false_elim
  iapply Hfalse
  iapply H.ihandle_mono e.fst $$ [] [] Hwp
  · iintro %a _; cases e.snd a
  · iintro !> %a _; cases e.snd a

omit Hin in
theorem wpi_assert {M} (P : Prop) [Decidable P] (Φ : PUnit → PROP) :
    P →
    Φ ⟨⟩ -∗
    WPi FailE.assert P @> H;M {{ Φ }} := by
  unfold FailE.assert
  iintro %x
  iintro H0_1
  simp_all only
  simp_all only [↓reduceIte]
  iapply IrisITreeScript.Core.wpi_pure
  iexact H0_1

end wpi_rules

section exec

open ITree.Exec

instance failEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  inv _ := iprop(True)
  adequate := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro %h0_4
    iintro %h0_5
    iintro H0_1
    iintro H0_2
    icases H0_2 with %H0_3
    simp_all only
    icases H0_1 with ⟨⟩

end exec
