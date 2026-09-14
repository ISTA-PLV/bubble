module

import Bubble

import Iris.ProofMode
public import ITree.Effects.Demonic
public import BubbleTest.IrisITree.Core.Wpi

@[expose] public section

namespace IrisITree.Effects

open Iris Iris.BI ITree IrisITree.Core ITree.Effects

section handler

variable {PROP : Type _} [BI PROP]

def demonicH (α : Type _) : IHandler PROP (demonicE α) where
  ihandle := λ _ Φ _ => iprop(∀ a, Φ a)
  ihandle_mono := by
    ibubble

instance demonicH_sequential {α : Type _} :
    Sequential (PROP := PROP) (demonicH (PROP := PROP) α) := by
  constructor
  unfold demonicH
  ibubble

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
  ibubble pureBy simp

end wpi_rules

section exec

open ITree.Exec IrisITree.Core

attribute [local simp] demonicH demonicEH

instance demonicEH_adequate {PROP : Type _} [BI PROP] [BIFUpdate PROP] {α : Type _} :
    SEHandlerAdequate (demonicH (PROP := PROP) α) (demonicEH α) where
  inv _ := iprop(emp)
  adequate := by
    intro i s C Φ1 Φ2 ⟨a, s', HC⟩
    ibubble pureStop <;> try simp
    exact HC

end exec
