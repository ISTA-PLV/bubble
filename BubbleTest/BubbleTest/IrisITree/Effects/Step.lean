-- SPDX-License-Identifier: Apache-2.0
module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITree.Core.Wpi
public import ITree.Effects.Step

public section

namespace IrisITree

open Iris Iris.BI ITree ITree.Effects

variable {PROP : Type _} [BI PROP]

/-- A logical modality used to interpret operational `step` events. -/
class StepMod (m : PROP → PROP) : Prop where
  mono (P Q : PROP) : (P -∗ Q) -∗ m P -∗ m Q

namespace StepMod

variable {m : PROP → PROP} [StepMod m]

-- [Warning] unrestricted recursive backward rule
@[ibubble 25%]
theorem map (P Q : PROP) : m P -∗ (P -∗ Q) -∗ m Q := by
  ibubble with [StepMod.mono]

theorem wand (P Q : PROP) : m iprop(P -∗ Q) -∗ P -∗ m Q := by
  ibubble

/-- Interpret a step with the identity modality, giving the *total* logic. -/
instance stepMod_id : StepMod (PROP := PROP) id where
  mono _ _ := by
    simp only [id]
    ibubble

/-- Interpret a step as one later modality, giving the *partial* logic. -/
instance stepMod_later : StepMod (PROP := PROP) BIBase.later where
  mono _ _ := by
    ibubble

end StepMod

/-- A step modality bundled with its monotonicity law, used as the mode of `WP`. -/
structure StepMode (PROP : Type _) [BI PROP] where
  m : PROP → PROP
  [step_mod : StepMod m]

attribute [instance] StepMode.step_mod

/-- Bundle a step modality and its inferred law for use in `WP e @ step[m]`. -/
notation "step[" m "]" => StepMode.mk (PROP := bi%) m

delab_rule StepMode.mk
  | `($_ $m) => `(step[$m])

section handler

/-- Interpret an operational step using the step modality `m`. -/
def stepH (m : PROP → PROP) [StepMod m] : IHandler PROP stepE where
  ihandle := fun _ Φ _ => m (Φ ⟨⟩)
  ihandle_mono := by
    ibubble

instance stepH_sequential {m : PROP → PROP} [StepMod m] : Sequential (stepH m):= by
  constructor; unfold stepH
  ibubble

/-- An identity step interpretation implies a later step interpretation. -/
instance stepH_ident_later :
    WandH (stepH (PROP := PROP) id) (stepH BIBase.later) := by
  constructor
  intro _ _ _
  exact entails_wand later_intro

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  {m : PROP → PROP} [StepMod m]
  [sub : stepE -< E] [Hin : InH (stepH m) H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] stepH

@[ibubble 75%]
theorem wpi_step Ms Me (Φ : PUnit → PROP) :
    m iprop(|={Ms, Me}=> Φ ()) -∗
    WPi step @> H; Ms,Me {{ Φ }} := by
  unfold step
  ibubble pureBy simp

end wpi_rules

section exec

open ITree.Exec

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

attribute [local simp] stepH stepEH Nat.zero_le

/-- Executing an identity-interpreted step requires no later credits. -/
instance stepEH_id_adequate :
    SEHandlerAdequate (stepH (PROP := PROP) id) (stepEH (fun _ => 0)) where
  inv _ := iprop(emp)
  adequate := by
    ibubble pureStop
    · simp
    · assumption

variable [BILaterCredits PROP] [BIFUpdLaterCredits PROP]

/-- Executing a later-interpreted step consumes one later credit. -/
instance stepEH_later_adequate :
    SEHandlerAdequate (stepH (PROP := PROP) BIBase.later) (stepEH (fun _ => 1)) where
  inv s := £ s.2.down
  adequate := by
    intro i ⟨st, sl⟩ C Φ₁ Φ₂ ⟨Hcredit, HC⟩
    simp only [stepH] at *
    iintro HΦ Hlc
    ihave Hparts : £ 1 ∗ £ (sl.down - 1) $$ [Hlc]
    · iapply lc_split.mp
      rw [Nat.add_sub_of_le Hcredit]
      iexact Hlc
    icases Hparts with ⟨Hone, Hrest⟩
    imod lc_fupd_elim_later $$ Hone HΦ with HΦ
    ibubble

end exec

end IrisITree
