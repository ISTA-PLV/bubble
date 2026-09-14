module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITreeScript.Core.Wpi
public import ITree.Effects.Step
public import Iris.Instances.Lib.FUpd

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree ITree.Effects IrisITreeScript.Core

section handler

variable {PROP : Type _} [BI PROP]

/-- A logical modality used to interpret operational `step` events. -/
class StepMod (PROP : Type _) [BI PROP] where
  apply : PROP → PROP
  mono (P Q : PROP) : ⊢@{PROP} (P -∗ Q) -∗ apply P -∗ apply Q

instance : CoeFun (StepMod PROP) (λ _ => PROP → PROP) where
  coe m := @StepMod.apply PROP _ m

namespace StepMod

-- [Warning] unrestricted recursive backward rule
@[ibubble 25%]
theorem map (m : StepMod PROP) (P Q : PROP) :
    ⊢@{PROP} m P -∗ (P -∗ Q) -∗ m Q := by
  iintro H0_1
  iintro H0_2
  iapply IrisITreeScript.Effects.StepMod.mono $$ [ H0_2 ]
  pick_goal 2
  iexact H0_1
  iintro H1_1
  iapply H0_2
  iexact H1_1

/-- Interpret a step without adding a logical modality. -/
@[reducible] def ident : StepMod PROP where
  apply P := P
  mono _ _ := by
    iintro H0_1
    iintro H0_2
    iapply H0_1
    iexact H0_2

/-- Interpret a step as one logical later. -/
@[reducible] def later : StepMod PROP where
  apply P := iprop(▷ P)
  mono _ _ := by
    iintro H0_1
    iintro H0_2
    iapply H0_1
    iexact H0_2

theorem wand (m : StepMod PROP) (P Q : PROP) :
    ⊢@{PROP} m iprop(P -∗ Q) -∗ P -∗ m Q := by
  iintro H0_1
  iintro H0_2
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_1 ]
  iexact H0_1
  iintro H1_1
  iapply H1_1
  iexact H0_2

end StepMod

/-- Interpret an operational step using `m`. -/
def stepH (m : StepMod PROP) : IHandler PROP stepE where
  ihandle := λ _ Φ _ => m (Φ ⟨⟩)
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
    iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_3 ]
    iexact H0_3
    iintro H1_1
    iapply H0_1
    iexact H1_1

instance stepH_sequential (m : StepMod PROP) : Sequential (stepH m) := by
  constructor; unfold stepH
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  simp_all only
  iexact H0_1

/-- An identity step interpretation implies a later step interpretation. -/
instance stepH_ident_later :
    WandH (stepH .ident (PROP := PROP)) (stepH .later) := by
  constructor
  intro _ _ _
  exact entails_wand later_intro

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  {m : StepMod PROP}
  [sub : stepE -< E] [Hin : InH (stepH m) H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] stepH

@[ibubble 75%]
theorem wpi_step M (Φ : PUnit → PROP) :
    m iprop(|={M}=> Φ ⟨⟩) -∗
    WPi step @> H; M {{ Φ }} := by
  change m iprop(|={M}=> Φ ⟨⟩) -∗
    WPi (@Effect.trigger stepE E sub ⟨⟩) @> H; M {{ Φ }}
  iintro H0_1
  simp_all only [stepH]
  iapply IrisITreeScript.Core.wpi_trigger
  simp_all only
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_1 ]
  iexact H0_1
  iapply Iris.fupd_mask_intro
  simp
  iintro H3_1
  iintro H3_2
  imod H3_1 with H3_1
  icases H3_1 with #H4_1
  iexact H3_2

end wpi_rules

section exec

open ITree.Exec

variable {GF : BundledGFunctors} [InvGS GF]

attribute [local simp] stepH stepEH Nat.zero_le

/-- Executing an identity-interpreted step requires no later credits. -/
instance stepEH_ident_adequate :
    SEHandlerAdequate (stepH (.ident (PROP := IProp GF))) (stepEH (λ _ => 0)) where
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
    simp_all only [stepEH, Nat.zero_le, Nat.sub_zero, _root_.true_and, stepH]
    iexists _
    iexists _
    imodintro
    isplit
    pick_goal 2
    isplit
    ipureintro
    pick_goal 2
    iexact H0_1
    pick_goal 2
    ipureintro
    pick_goal 6
    pick_goal 6
    pick_goal 6
    pick_goal 5
    pick_goal 5
    pick_goal 6
    · simp
    · assumption

/-- Executing a later-interpreted step consumes one later credit. -/
instance stepEH_later_adequate :
    SEHandlerAdequate (stepH (.later (PROP := IProp GF))) (stepEH (λ _ => 1)) where
  inv s := £ s.2.down
  adequate := by
    intro i s C Φ₁ Φ₂ Hhandle
    simp only [stepH, stepEH] at *
    obtain ⟨Hcredit, HC⟩ := Hhandle
    iintro HΦ Hlc
    ihave Hparts : £ 1 ∗ £ (s.2.down - 1) $$ [Hlc]
    · iapply lc_split.mp
      rw [Nat.add_sub_of_le Hcredit]
      iexact Hlc
    icases Hparts with ⟨Hone, Hrest⟩
    imod lc_fupd_elim_later $$ Hone HΦ with HΦ
    iexists _
    iexists _
    isplitl []
    (ipureintro; assumption)
    simp_all only
    isplitl [Hrest]
    iexact Hrest
    iexact HΦ

end exec
