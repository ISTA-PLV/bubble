module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Fail
public import BubbleTest.IrisITreeBubble.Core.Wpi

@[expose] public section

namespace IrisITreeBubble.Effects

open Iris Iris.BI ITree IrisITreeBubble.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def failH : IHandler PROP failE where
  ihandle := λ _ _ _ => iprop(False)
  ihandle_mono := by
    ibubble

instance failH_sequential : Sequential (PROP := PROP) failH := by
  constructor
  ibubble

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
  ibubble

end wpi_rules

section exec

open ITree.Exec

instance failEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] :
    SEHandlerAdequate (failH (PROP := PROP)) failEH where
  inv _ := iprop(True)
  adequate := by
    ibubble

end exec
