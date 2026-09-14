module

import Bubble

import Iris.BI.Lib.Fixpoint
public import Iris.BI.WeakestPre
public import Iris.ProofMode.Classes
import Iris.ProofMode
public import ITree.Definition
public import ITree.Effect
public import BubbleTest.IrisITreeBubble.Core.Handler
import BubbleTest.IrisITreeBubble.Core.ITree

namespace IrisITreeBubble.Core

open Iris BI ITree ProofMode

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

public section

section wp_itree_def

variable {E} (H : IHandler PROP E)

@[expose]
def wpiF {R} (wpi : CoPset → ITree E R → (R → PROP) → PROP) :
    CoPset → CoPset → ITree E R → (R → PROP) → PROP :=
  λ Ms Me t Φ =>
    iprop(
      |={Ms, ∅}=> match t.unfold with
        | ITreeF.ret r => iprop(|={∅, Me}=> Φ r)
        | ITreeF.tau t' => wpi ∅ t' Φ
        | ITreeF.vis i k => H.ihandle i
          (λ a => wpi ∅ (k a) Φ)
          (λ a => wpi ∅ (k a) (λ _ => iprop(False)))
    )

private def wpiF' {R} (Me : CoPset) (wpi : DiscreteO CoPset × ITree E R × (R → PROP) → PROP) :
    DiscreteO CoPset × ITree E R × (R → PROP) → PROP :=
  λ ⟨Ms, t, Φ⟩ => wpiF H (λ Ms t Φ => wpi ⟨⟨Ms⟩, t, Φ⟩) Ms.1 Me t Φ

attribute [local ibubble 10%] IHandler.ihandle_mono

@[ibubble 75%]
theorem wpiF_mono {R} (wp1 wp2 : CoPset → ITree E R → (R → PROP) → PROP) Me :
    □ (∀ t Φ, wp1 ∅ t Φ -∗ wp2 ∅ t Φ) -∗
    ∀ Ms t Φ, wpiF H wp1 Ms Me t Φ -∗ wpiF H wp2 Ms Me t Φ := by
  unfold wpiF; iintro #Hwand %Ms %t
  cases h : t.unfold <;> ibubble

private instance {R Me} : BIMonoPred (wpiF' (R:=R) H Me) where
  mono_pred := by
    unfold wpiF'
    ibubble

  mono_pred_ne := by
    intro wp Hwp; constructor; intro n ⟨Ms1, t1, Ψ1⟩ ⟨Ms2, t2, Ψ2⟩ ⟨HMs, Ht, HΨ⟩
    simp at HMs Ht HΨ; subst HMs Ht
    unfold wpiF'; apply BIFUpdate.ne.ne
    cases t1 <;> simp
    case ret r => apply BIFUpdate.ne.ne; apply HΨ
    case tau t' => apply Hwp.ne; refine ⟨.rfl, .rfl, HΨ⟩
    case vis i k =>
      apply OFE.NonExpansive₂.ne <;> intro a
      · apply Hwp.ne; refine ⟨.rfl, .rfl, HΨ⟩
      · apply Hwp.ne; refine ⟨.rfl, .rfl, .rfl⟩

/-- `wpi` is a weakest precondition for `ITree` -/
def wpi {E R} (H : IHandler PROP E) (Ms Me : CoPset) (t : ITree E R) (Φ : R → PROP) : PROP :=
  bi_least_fixpoint (wpiF' H Me) (⟨Ms⟩, t, Φ)

instance {R Ms Me} {t : ITree E R} : OFE.NonExpansive (wpi H Ms Me t) := by
  constructor; intro n Φ₁ Φ₂ HΦ
  exact OFE.NonExpansive.ne (f := bi_least_fixpoint (wpiF' H Me)) ⟨rfl, rfl, HΦ⟩

end wp_itree_def

syntax (name := wpiNotation) "WPi " term:20 " @> " term:20 "; " term:max
  ("," term:max)? wpPostcond : term

@[macro wpiNotation]
meta def wpiMacro : Lean.Macro := λ stx => do
  match stx with
  | `(WPi $t:term @> $H:term; $Ms:term, $Me:term $postcond:wpPostcond) =>
    let (Φ, _) ← Iris.parseWpPostcond postcond
    `(wpi (H := $H) $Ms $Me $t $Φ)
  | `(WPi $t:term @> $H:term; $M:term $postcond:wpPostcond) =>
    let (Φ, _) ← Iris.parseWpPostcond postcond
    `(wpi (H := $H) $M $M $t $Φ)
  | _ => Lean.Macro.throwUnsupported

delab_rule wpi
  | `($_ $H $Ms $Me $t (fun $v:ident => $Q)) => do
    let inner ← Iris.unexpandWpPostcondInner (← `(fun $v => $Q))
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $inner }})
    else `(WPi $t @> $H;$Ms,$Me {{ $inner }})
  | `($_ $H $Ms $Me $t $Φ) => do
    let inner ← Iris.unexpandWpPostcondInner Φ
    if Ms == Me then `(WPi $t @> $H;$Ms {{ $inner }})
    else `(WPi $t @> $H;$Ms, $Me {{ $inner }})

section wpi_unfold

variable {E} {Ms Me : CoPset} {H : IHandler PROP E}

theorem wpi_unfold {R} (t : ITree E R) Φ :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ wpiF H (λ Ms t Φ => WPi t @> H;Ms,Me {{ Φ }}) Ms Me t Φ := by
  apply equiv_iff.mp
  apply least_fixpoint_unfold

theorem fupd_wpi_empty (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms, ∅}=> WPi t @> H;∅,Me {{ Φ }} :=
    (wpi_unfold _ _).trans <| by
  unfold wpiF; isplit <;> iintro >Hwp
  · imodintro; iapply wpi_unfold;
    unfold wpiF; ibubble
  · ihave H := wpi_unfold $$ Hwp;
    unfold wpiF; ibubble

section instances

instance elimModal_fupd_wpi p E1 E2 E3 (P : PROP) :
    ElimModal True p io false
      iprop(|={E1,E2}=> P) P
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;E2,E3 {{Φ}}) where
  elim_modal _ := by
    cases p <;> simp
    · iintro ⟨HP, Hwand⟩; iapply fupd_wpi_empty
      imod HP; ihave Hwp := Hwand $$ HP
      iapply (fupd_wpi_empty Φ).mp $$ Hwp
    · iintro ⟨#HP, Hwand⟩; iapply fupd_wpi_empty
      imod HP; ihave Hwp := Hwand $$ HP
      iapply (fupd_wpi_empty Φ).mp $$ Hwp

instance elimModal_wpi_wpi p H1 H2 (t1 : ITree E1 R1) (t2 : ITree E2 R2) Ms Me1 Me2 Φ1 Φ2 :
    ElimModal (PROP:=PROP) True p io false
      iprop(WPi t1 @> H1;Ms,Me1 {{Φ1}}) iprop(WPi t1 @> H1;∅,Me1 {{Φ1}})
      iprop(WPi t2 @> H2;Ms,Me2 {{Φ2}}) iprop(WPi t2 @> H2;∅,Me2 {{Φ2}}) where
  elim_modal _ := by
    cases p <;> simp
    all_goals
      iintro ⟨HΦ, Hwand⟩; ihave HΦ := fupd_wpi_empty $$ HΦ
      ibubble with [fupd_wpi_empty 75%]

instance elimModal_wpi_fupd p E1 E2 E3 (P : PROP) :
    ElimModal True p io false
      iprop(WPi t @> H;E1,E3 {{Φ}}) iprop(WPi t @> H;∅,E3 {{Φ}})
      iprop(|={E1,E2}=> P) iprop(|={∅,E2}=> P) where
  elim_modal _ := by
    cases p <;> simp
    all_goals
      iintro ⟨HΦ, Hwand⟩; ihave HΦ := fupd_wpi_empty $$ HΦ
      ibubble

end instances

theorem fupd_wpi (Φ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} ⊣⊢ |={Ms}=> WPi t @> H;Ms,Me {{ Φ }} := by
  ibubble

theorem wpi_pure' {R} (Φ : R → PROP) (r : R) :
  WPi pure r @> H;Ms,Me {{ Φ }} ⊣⊢ (|={Ms, Me}=> Φ r) := (wpi_unfold _ _).trans <| by
  unfold wpiF
  ibubble pureBy simp with [fupd_mask_intro]

@[ibubble 75%]
theorem wpi_pure {R} (M : CoPset) (Φ : R → PROP) (r : R) :
    Φ r ⊢ WPi pure r @> H; M {{ Φ }} := by
  ibubble with [wpi_pure']

theorem wpi_tau {R} (Φ : R → PROP) (t : ITree E R) :
    (WPi t.tau @> H;Ms,Me {{ Φ }}) ⊣⊢ (WPi t @> H;Ms,Me {{ Φ }}) := (wpi_unfold _ _).trans <| by
  unfold wpiF
  ibubble

@[ibubble 75%]
theorem wpi_tau' {R} (Φ : R → PROP) (t : ITree E R) :
    WPi t @> H;Ms,Me {{ Φ }} ⊢ WPi t.tau @> H;Ms,Me {{ Φ }} := by
  ibubble with [wpi_tau]

theorem wpi_vis {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (WPi (ITree.vis i k) @> H;Ms,Me {{ Φ }}) ⊣⊢
    (|={Ms, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (λ a => WPi (k a) @> H; ∅,Me {{ λ _ => iprop(False) }})) :=
  wpi_unfold _ _

@[ibubble 75%]
theorem wpi_vis' {R} (Φ : R → PROP) (i : E.I) (k : E.O i → ITree E R) :
    (|={Ms, ∅}=> H.ihandle i
      (λ a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (λ a => WPi (k a) @> H; ∅,Me {{ λ _ => iprop(False) }})) -∗
    (WPi (ITree.vis i k) @> H;Ms,Me {{ Φ }}) := by
  ibubble with [wpi_vis]

theorem wpi_trigger_bind {E' A} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (k : E'.O i → ITree E A) (Φ : A → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (λ a => WPi (k a) @> H; ∅,Me {{ Φ }})
      (λ a => WPi (k a) @> H; ∅,Me {{ λ _ => iprop(False) }})) -∗
    WPi E'.trigger i >>= k @> H; Ms, Me {{ Φ }} := by
  iintro >HH; simp [Effect.trigger]
  iapply wpi_vis; imodintro
  let e := Subeffect.map (E₂ := E) i
  iapply H.ihandle_mono e.fst (λ a => WPi (k (e.snd a)) @> H; ∅,Me {{ Φ }}) _
    (λ a => WPi (k (e.snd a)) @> H; ∅,Me {{ fun _ => iprop(False) }}) _
  · ibubble
  · ibubble
  /- [Note]: `HH` is needed to infer the source event hidden by `Subeffect.map` -/
  · iapply InH.is_inH $$ HH

@[ibubble 25%]
theorem wpi_trigger {E'} [E' -< E] (H' : IHandler PROP E') [InH H' H]
    (i : E'.I) (Φ : E'.O i → PROP) :
    (|={Ms, ∅}=> H'.ihandle i
      (λ a => iprop(|={∅, Me}=> Φ a))
      (λ _ => iprop(False))) -∗
    WPi (E'.trigger i) @> H; Ms,Me {{ Φ }} := by
  iintro HH; unfold Effect.trigger
  iapply wpi_vis; imod HH; imodintro
  let e := Subeffect.map (E₂ := E) i
  iapply H.ihandle_mono e.fst (λ a => iprop(|={∅, Me}=> Φ (e.snd a))) _
    (λ _ => iprop(False)) _
  · ibubble
  · ibubble
  · iapply InH.is_inH $$ HH

end wpi_unfold

section wpi_induction

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

theorem wpi_ind_mask (G : CoPset → ITree E R → (R → PROP) → PROP)
   [∀ Ms t, OFE.NonExpansive (G Ms t)] :
    □ (∀ Ms t Φ, wpiF H (λ Ms' t' Ψ => iprop(G Ms' t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }})) Ms Me t Φ -∗ G Ms t Φ) ⊢
    (∀ Ms t Φ, WPi t @> H;Ms,Me {{ Φ }} -∗ G Ms t Φ) := by
  iintro #HPre %Ms %t %Φ Hwp; unfold wpi
  let G' : (DiscreteO CoPset × _ × _) → _ := λ ⟨⟨Ms⟩, t, Φ⟩ => G Ms t Φ
  have : OFE.NonExpansive G' := by
    constructor; intro n ⟨⟨Ms₁⟩, t₁, Φ₁⟩ ⟨⟨Ms₂⟩, t₂, Φ₂⟩ ⟨rfl, Ht, HΦ⟩
    simp [G'] at *; subst Ht; apply OFE.NonExpansive.ne HΦ
  iapply least_fixpoint_ind (wpiF' H Me) G' $$ [] %⟨⟨Ms⟩, t, Φ⟩ Hwp
  unfold wpiF'
  ibubble

variable (G : ITree E R → (R → PROP) → PROP) [∀ t, OFE.NonExpansive (G t)]

theorem wpi_ind :
    □ (∀ t Φ, wpiF H (λ Ms' t' Ψ => iprop(G t' Ψ ∧ WPi t' @> H;Ms',Me {{ Ψ }})) ∅ Me t Φ -∗ G t Φ) ⊢
    (∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ) := by
  iintro #HPre %t %Φ Hwp
  let G' := λ (Ms : CoPset) t Φ => iprop(<affine> ⌜Ms = ∅⌝ -∗ G t Φ)
  have : ∀ Ms t, OFE.NonExpansive (G' Ms t) := by
    intro Ms t; constructor; intro n Φ₁ Φ₂ HΦ; simp [G'];
    exact wand_ne.ne .rfl <| OFE.NonExpansive.ne HΦ
  iapply wpi_ind_mask G' $$ [] Hwp <;> ibubble pureBy simp

theorem wpi_iter :
    □ (∀ t Φ, wpiF H (λ _ => G) ∅ Me t Φ -∗ G t Φ) ⊢
    (∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ) := by
  ibubble with [wpi_ind 25%]

theorem wpi_iter' :
    □ (∀ Φ r, (|={∅, Me}=> Φ r) -∗ G (pure r) Φ) -∗
    □ (∀ Φ t, (|={∅}=> G t Φ) -∗ G (ITree.tau t) Φ) -∗
    □ (∀ Φ i k, (|={∅}=> H.ihandle i
         (λ a => G (k a) Φ)
         (λ a => G (k a) (λ _ => iprop(False)))) -∗
           G (ITree.vis i k) Φ) -∗
    (∀ t Φ, WPi t @> H;∅,Me {{ Φ }} -∗ G t Φ) := by
  iintro #HPure #HTau #HVis %t %Φ
  iapply wpi_iter $$ []
  iintro !> %t %Φ HwpiF; unfold wpiF
  cases t <;> ibubble

end wpi_induction

section wpi_lemmas

variable {E R} {Ms Me : CoPset} {H : IHandler PROP E}

attribute [local ibubble 10%] IHandler.ihandle_mono

@[local ibubble 25%]
theorem wpi_wand (Φ Ψ : R → PROP) :
    WPi t @> H;Ms,Me {{ Φ }} -∗
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @> H;Ms,Me {{ Ψ }} := by
  iintro >Hwp Hwand
  let G := λ t (Φ : R → PROP) =>
    iprop(∀ Ψ, (∀ r, Φ r -∗ Ψ r) -∗ WPi t @> H;∅,Me {{ Ψ }})
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor
    intro n x₁ x₂ Hx; simp [G]
    refine forall_ne λ Ψ => wand_ne.ne ?_ .rfl
    exact forall_ne λ r => wand_ne.ne (Hx r) .rfl
  iapply wpi_iter' G $$ [] [] [] Hwp Hwand <;> ibubble

@[local ibubble 25%]
theorem wpi_fupd_empty_2 (Φ : R → PROP) :
    WPi t @> H; Ms, ∅ {{ v, iprop(|={∅, Me}=> Φ v) }} ⊢
    WPi t @> H; Ms, Me {{ Φ }} := by
  iintro >Hwp
  let G := λ t (Ψ : R → PROP) =>
    iprop(∀ Φ, (∀ r, Ψ r -∗ |={∅, Me}=> Φ r) -∗ WPi t @> H;∅,Me {{ Φ }})
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor
    intro n Ψ₁ Ψ₂ HΨ; simp [G]
    refine forall_ne λ Φ => wand_ne.ne ?_ .rfl
    exact forall_ne λ r => wand_ne.ne (HΨ r) .rfl
  iapply wpi_iter' G $$ [] [] [] Hwp <;> ibubble

@[local ibubble 25%]
theorem wpi_fupd_empty_1 (Φ : R → PROP) :
    WPi t @> H; Ms, Me {{ Φ }} ⊢
    WPi t @> H; Ms, ∅ {{ v, iprop(|={∅, Me}=> Φ v) }} := by
  iintro >Hwp
  let G := λ t (Ψ : R → PROP) =>
    WPi t @> H; ∅,∅ {{ v, iprop(|={∅, Me}=> Ψ v) }}
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor; intro n Ψ₁ Ψ₂ HΨ; simp [G]
    exact OFE.NonExpansive.ne (f := wpi H ∅ ∅ t) <|
      λ v => BIFUpdate.ne.ne (HΨ v)
  iapply wpi_iter' G $$ [] [] [] Hwp
  · ibubble
  · ibubble
  · iintro !> %Ψ %i %k >HΨ; simp [G]
    iapply wpi_vis; imodintro
    iapply H.ihandle_mono $$ [] [] HΨ <;> ibubble

theorem wpi_fupd_empty (Φ : R → PROP) :
    WPi t @> H; Ms, Me {{ Φ }} ⊣⊢
    WPi t @> H; Ms, ∅ {{ v, iprop(|={∅, Me}=> Φ v) }} := by
  ibubble

theorem wpi_fupd (Φ : R → PROP) :
    (WPi t @> H; Ms, Me {{ Φ }}) ⊣⊢
    (WPi t @> H; Ms, Me {{ v, iprop(|={Me}=> Φ v) }}) := by
  ibubble

theorem wpi_bind' {A} M' t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms, M' {{ r, WPi k r @> H;M',Me {{ Φ }} }} ⊢
    WPi t >>= k @> H; Ms, Me {{ Φ }} := by
  iintro >Hwp
  let G := λ t (Φ : A → PROP) =>
    iprop(∀ Ψ, (∀ r, Φ r -∗ WPi k r @> H; M', Me {{ Ψ }})
      -∗ WPi t >>= k @> H; ∅, Me {{ Ψ }})
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor; intro n Φ₁ Φ₂ HΦ; simp [G]
    refine forall_ne λ x => wand_ne.ne ?_ .rfl
    exact forall_ne λ x => wand_ne.ne (HΦ x) .rfl
  iapply wpi_iter' G $$ [] [] [] Hwp <;> ibubble

/-- specialized version where M' = Ms. This is especially useful for the Ms = Me case. -/
@[ibubble 75%]
theorem wpi_bind {A} t (k : A → ITree E R) (Φ : R → PROP) :
    WPi t @> H; Ms {{ r, WPi k r @> H;Ms,Me {{ Φ }} }} ⊢
    WPi t >>= k @> H; Ms, Me {{ Φ }} := wpi_bind' _ _ _ _

end wpi_lemmas

section wp_itree_translation

attribute [local ibubble 10%] IHandler.ihandle_mono

-- `f` can interpret each event `E1` as an `itree E2 E1.I`, as a way to
-- "translate" from events `E1` to `E2`
variable {E1 E2 : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  (f : (i : E1.I) → ITree E2 (E1.O i))

/-- Translate a WPi proof across handlers by interpreting each `E₁` event as an `E₂` itree. -/
@[ibubble 10%]
theorem wpi_translation {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} -∗
    □ (∀ i (k : E1.O i → ITree E1 R) Ψ,
      H1.ihandle i
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅,Me {{ Ψ }})
        (λ a => WPi (ITree.interp f (k a)) @> H2; ∅,Me {{ λ _ => iprop(False) }}) -∗
      WPi (f i >>= λ a => ITree.interp f (k a)) @> H2; ∅,Me {{ Ψ }}) -∗
    WPi (ITree.interp f t) @> H2; Ms, Me {{ Φ }} := by
  iintro >Hwp #HH
  let G : ITree E1 R → (R → PROP) → PROP := λ t Φ => WPi (ITree.interp f t) @> H2; ∅,Me {{Φ}}
  iapply (wpi_iter' G) $$ [] [] [] Hwp <;> ibubble

/-- A sequential special case of `wpi_translation` with a simpler handler-side premise. -/
theorem wpi_translation_seq {R} (t : ITree E1 R) (Φ : R → PROP) :
    WPi t @> H1; Ms,Me {{ Φ }} -∗
    □ (∀ i Ψ, H1.ihandle i Ψ (λ _ => iprop(True)) -∗
        WPi (f i) @> H2; ∅ {{ Ψ }}) -∗
    WPi (ITree.interp f t) @> H2; Ms,Me {{ Φ }} := by
  ibubble pureBy simp

end wp_itree_translation

section wp_itree_mono

variable {E : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {H1 : IHandler PROP E} {H2 : IHandler PROP E}
  [Hwand : WandH H1 H2]

attribute [local ibubble 10%] IHandler.ihandle_mono WandH.is_wandH
attribute [local simp] Effect.trigger

theorem wpi_wandH {R} (t : ITree E R) (Φ : R → PROP) :
    WPi t @> H1; Ms, Me {{ Φ }} ⊢ WPi t @> H2; Ms, Me {{ Φ }} := by
  iintro Hwp
  have ht : t = t.interp (λ i => E.trigger i) := by simp [-Effect.trigger]
  rw (occs:=[2]) [ht]; clear ht
  ibubble

end wp_itree_mono

section wp_itree_inH

variable {E1 E2 : Effect} {Ms Me : CoPset}
  {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]
  {H1 : IHandler PROP E1} {H2 : IHandler PROP E2}
  [sub : E1 -< E2] [Hin : InH H1 H2]

attribute [local ibubble 10%] IHandler.ihandle_mono
attribute [local ibubble 25%] wpi_trigger_bind wpi_fupd_empty_2 InH.is_inH

@[local ibubble 50%]
theorem wpi_inH_1 (t : ITree E1 R) (Φ : R → PROP) :
    (WPi t @> H1; Ms, Me {{ Φ }}) -∗
    (WPi (t.interp (λ i => E1.trigger i)) @> H2; Ms, Me {{ Φ }}) := by
  ibubble

@[local ibubble 50%]
theorem wpi_inH_2 (t : ITree E1 R) (Φ : R → PROP) :
    (WPi (t.interp (λ i => E1.trigger i)) @> H2; Ms, Me {{ Φ }}) -∗
    (WPi t @> H1; Ms, Me {{ Φ }}) := by
  let emb : (i : E1.I) → ITree E2 (E1.O i) := λ i => E1.trigger i
  let G : ITree E2 R → (R → PROP) → PROP := λ u Ψ =>
    iprop(∀ t', ⌜ITree.interp emb t' = u⌝ -∗ (WPi t' @> H1; ∅ {{ Ψ }}))
  have : ∀ t, OFE.NonExpansive (G t) := by
    intro t; constructor; intro n x₁ x₂ Hx; simp [G]
    exact forall_ne λ t' => wand_ne.ne .rfl $ OFE.NonExpansive.ne Hx
  ihave Hgen : (∀ t Ψ, (WPi t @> H2; ∅ {{ Ψ }}) -∗ G t Ψ) $$ []
  · iapply wpi_iter' G
    · iintro !> %Φ %r HΦ; simp [G]; iintro %t' %Heq
      rcases interp_ret_inv Heq with ⟨rfl⟩
      ibubble
    · iintro !> %Ψ %u Hu; simp [G]; iintro %t' %Heq
      rcases interp_tau_inv Heq with ⟨t1, rfl, Heq1⟩
      ibubble noSimp pureBy rfl
    · iintro !> %Ψ %i %k >Hik; simp [G]; iintro %t' %Heq
      rcases interp_vis_inv Heq with ⟨i', k', rfl, rfl, rfl⟩
      ibubble pureBy (first | assumption | rfl)
  iintro Hwp; simp [G];
  ihave Hwp := wpi_fupd_empty $$ Hwp
  ibubble pureBy rfl

theorem wpi_inH (t : ITree E1 R) (Φ : R → PROP) :
    (WPi t @> H1; Ms, Me {{ Φ }}) ⊣⊢
    (WPi (t.interp (λ i => E1.trigger i)) @> H2; Ms, Me {{ Φ }}) := by
  ibubble

end wp_itree_inH
