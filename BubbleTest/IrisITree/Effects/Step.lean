module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITree.Core.Wpi
public import ITree.Effects.Step
public import Iris.Instances.Lib.FUpd

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree ITree.Effects IrisITree.Core

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
  ibubble with [StepMod.mono]

/-- Interpret a step without adding a logical modality. -/
@[reducible] def ident : StepMod PROP where
  apply P := P
  mono _ _ := by
    ibubble

/-- Interpret a step as one logical later. -/
@[reducible] def later : StepMod PROP where
  apply P := iprop(▷ P)
  mono _ _ := by
    ibubble

theorem wand (m : StepMod PROP) (P Q : PROP) :
    ⊢@{PROP} m iprop(P -∗ Q) -∗ P -∗ m Q := by
  ibubble

end StepMod

/-- Interpret an operational step using `m`. -/
def stepH (m : StepMod PROP) : IHandler PROP stepE where
  ihandle := λ _ Φ _ => m (Φ ⟨⟩)
  ihandle_mono := by
    ibubble

instance stepH_sequential (m : StepMod PROP) : Sequential (stepH m) := by
  constructor; unfold stepH
  ibubble

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
  ibubble pureBy simp

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
    ibubble pureStop
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
    ibubble

end exec
