module

public import BubbleTest.IrisITree.Effects.Conc
public import Iris.ProofMode

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree ITree.Effects IrisITree.Core

section

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  [concE -< E] [Hin : InH concH H]

set_option Elab.async false in
#time
theorem wpi_fork_generated M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, iprop(True) }} -∗
    WPi fork t @> H; M {{Φ}} := by
  unfold fork
  iintro HΦ Ht
  iapply wpi_trigger_bind
  simp_all only [concH]
  iapply Iris.fupd_mask_intro
  simp
  iintro H1_1
  isplitl [HΦ H1_1]
  imod H1_1 with H1_1
  icases H1_1 with #H3_1
  iapply IrisITree.Core.wpi_pure
  iexact HΦ
  iapply IrisITree.Core.wpi_bind'
  imod Ht with Ht
  iapply IrisITree.Core.wpi_wand $$ [Ht]
  iexact Ht
  imodintro
  iintro %r
  iintro H6_1
  iapply IrisITree.Effects.wpi_kill
  icases H6_1 with %H7_1
  simp_all only
  ipureintro
  simp

end

end IrisITree.Effects
