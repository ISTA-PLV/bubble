module

import Bubble

public import BubbleTest.IrisITreeScript.Core.Wpi
public import BubbleTest.IrisITreeScript.Effects
public import BubbleTest.IrisITreeScript.HeapLang.Semantics
public import Iris.BI.WeakestPre
public import Iris.Instances.IProp
public import Iris.Instances.Lib.FUpd

attribute [-simp] LawfulMonad.bind_pure_comp

@[expose] public section
namespace IrisITreeScript.HeapLang

open Iris IrisITreeScript.Core Iris.HeapLang IrisITreeScript.Effects ITree ITree.Effects

class heaplangHGpreS (GF : BundledGFunctors) where
  heaplangH_heapHG : heapHGpreS GF Loc Val

attribute [reducible, instance] heaplangHGpreS.heaplangH_heapHG

class heaplangHGS (GF : BundledGFunctors) where
  heaplangH_heapHGS : heapHGS GF Loc Val

attribute [reducible, instance] heaplangHGS.heaplangH_heapHGS

instance lawfulLoc_heaplang : LawfulLoc Loc where
  decEq := inferInstance
  add_zero l := by ext; simp
  add_nat_inj l := by
    intro i j Hij
    have Hn := congrArg Loc.n Hij
    simp at Hn
    omega
  add_pos_nle := by
    intro l m
    simp [compare, compareOfLessAndEq, Ordering.isLE]
    grind

section handler

variable {GF} [InvGS GF] [heaplangHGS GF]

def heaplangH (m : StepMod (IProp GF)) : IHandler (IProp GF) heaplangE :=
  concH ⊕ₕ heapH ⊕ₕ failH ⊕ₕ demonicH Loc ⊕ₕ stepH m

instance inH_conc_heaplang (m : StepMod (IProp GF)) :
    InH concH (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_heap_heaplang (m : StepMod (IProp GF)) :
    InH (heapH (Loc := Loc) (Val := Val)) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_fail_heaplang (m : StepMod (IProp GF)) :
    InH failH (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_demonic_heaplang (m : StepMod (IProp GF)) :
    InH (demonicH Loc) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance inH_step_heaplang (m : StepMod (IProp GF)) :
    InH (stepH m) (heaplangH m) := by
  unfold heaplangH
  infer_instance

instance wandH_heaplang_ident_later :
    WandH (heaplangH (.ident (PROP := IProp GF))) (heaplangH .later) := by
  unfold heaplangH
  infer_instance

instance wp_heaplang : Wp (IProp GF) Exp Val (StepMod (IProp GF)) where
  wp m M e Φ := WPi e.denote @> heaplangH m; M {{ Φ }}

end handler

section wpi_rules

variable {GF} [InvGS GF] [heaplangHGS GF]
  {m : StepMod (IProp GF)}

@[ibubble 75%]
theorem wpi_step_pure E (v : Val) (Φ : Val → IProp GF) :
    m (Φ v) -∗
    WPi (do
      step
      pure v) @> heaplangH m; E {{ Φ }} := by
  iintro H0_1
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_step
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_1 ]
  iexact H0_1
  iintro H3_1
  iapply IrisITreeScript.Core.wpi_pure
  iexact H3_1

attribute [local simp] Exp.yieldIfNotVal

@[ibubble 75%]
theorem wpi_yieldIfNotVal (e : Exp) (Φ : Unit → IProp GF) :
    Φ () -∗
    WPi e.yieldIfNotVal @> heaplangH m; ⊤ {{ Φ }} := by
  cases e
  · iintro H0_1
    simp_all only [Exp.yieldIfNotVal]
    iapply IrisITreeScript.Core.wpi_pure
    iexact H0_1
  all_goals
    iintro H0_1
    simp_all only [Exp.yieldIfNotVal]
    iapply IrisITreeScript.Effects.wpi_yield
    iexact H0_1

@[ibubble 75%]
theorem wpi_cont (e : Exp) (Φ : Val → IProp GF) :
    m (WP e @ m ; ⊤ {{ Φ }}) -∗
    WPi (do
      step
      e.yieldIfNotVal
      e.denote) @> heaplangH m; ⊤ {{ Φ }} := by
  iintro H0_1
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_step
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_1 ]
  iexact H0_1
  iintro H3_1
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.HeapLang.wpi_yieldIfNotVal
  iexact H3_1

end wpi_rules

section wp_rules

variable {GF} [InvGS GF] [heaplangHGS GF]
  {m : StepMod (IProp GF)}

attribute [local ibubble 10%] wpi_wand

@[local simp]
theorem wp_unfold {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
  WP e @ m; M {{ Φ }} = WPi e.denote @> heaplangH m; M {{ Φ }} := rfl

/-- The identity (total) WP implies the later (partial) WP. -/
theorem wp_later_weaken {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    WP e @ (StepMod.ident (PROP := IProp GF)); M {{ Φ }} -∗
    WP e @ (StepMod.later (PROP := IProp GF)); M {{ Φ }} := by
  iintro H0_1
  simp_all only [wp_unfold]
  iapply IrisITreeScript.Core.wpi_wandH
  pick_goal 2
  iexact H0_1
  infer_instance

theorem wp_wand {M : CoPset} (e : Exp) (Φ Ψ : Val → IProp GF) :
    WP e @ m ; M {{ Φ }} -∗
    (∀ v, Φ v -∗ Ψ v) -∗
    WP e @ m ; M {{ Ψ }} := by
  iintro H0_1
  iintro H0_2
  simp_all only [wp_unfold]
  iapply IrisITreeScript.Core.wpi_wand $$ [ H0_1 ]
  iexact H0_1
  iintro %r
  iintro H1_1
  iapply H0_2
  iexact H1_1

theorem wp_frame_l {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    P ∗ WP e @ m; M {{ Φ }} -∗ WP e @ m; M {{v , P ∗ Φ v}} := by
  iintro H0_1
  icases H0_1 with ⟨H0_2, H0_3⟩
  simp_all only [wp_unfold]
  iapply IrisITreeScript.Core.wpi_wand $$ [ H0_3 ]
  iexact H0_3
  iintro %r
  iintro H1_1
  isplitl [H0_2]
  iexact H0_2
  iexact H1_1

theorem wp_atomic E1 E2 (e : Exp) (Φ : Val → IProp GF) :
    (|={E1,E2}=> WP e @ m ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ m ; E1 {{ Φ }} := by
  simp only [wp_unfold]
  iintro > >Hwp
  ihave Hwp := wpi_fupd_empty $$ Hwp
  iapply IrisITreeScript.Core.wpi_fupd_empty_2
  iapply IrisITreeScript.Core.wpi_wand $$ [ Hwp ]
  iexact Hwp
  iintro %r
  iintro H2_1
  imod H2_1 with H2_1
  iexact H2_1

theorem fupd_wp {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (|={M}=> WP e @ m ; M {{ v, Φ v }}) ⊢ WP e @ m ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (fupd_wpi _).2

theorem wp_fupd {M : CoPset} (e : Exp) (Φ : Val → IProp GF) :
    (WP e @ m ; M {{ v, |={M}=> Φ v }}) ⊢ WP e @ m ; M {{ Φ }} := by
  simp only [wp_unfold]
  iapply (wpi_fupd _).2

@[ibubble 75%]
theorem wp_val {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    Φ v -∗
    WP hl(v(&v)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, ← val_to_ofVal, Exp.denote.eq_1]
  iintro H0_1
  iapply IrisITreeScript.Core.wpi_pure
  iexact H0_1

theorem wp_unop {M : CoPset} (op : UnOp) (v v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v = pure v'⌝ -∗
    m (Φ v') -∗
    WP (Exp.unop op (Exp.val v)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_5, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  iintro H0_2
  icases H0_1 with %H0_3
  simp_all only [↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_2

theorem wp_binop {M : CoPset} (op : BinOp) (v₁ v₂ v' : Val) (Φ : Val → IProp GF) :
    ⌜op.denote v₁ v₂ = pure v'⌝ -∗
    m (Φ v') -∗
    WP (Exp.binop op (Exp.val v₁) (Exp.val v₂)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_6, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  iintro H0_2
  icases H0_1 with %H0_3
  simp_all only [↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_2

theorem wp_if_true (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP e₁ @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool true))) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, Val.bool!, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_cont
  simp_all only [wp_unfold]
  iexact H0_1

theorem wp_if_false (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP e₂ @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.if (Exp.val (Val.lit (BaseLit.bool false))) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_7, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, Val.bool!, pure_bind, Bool.false_eq_true]
  iapply IrisITreeScript.HeapLang.wpi_cont
  simp_all only [wp_unfold]
  iexact H0_1

theorem wp_app (f x : Binder) (v : Val) (e : Exp) (Φ : Val → IProp GF) :
    m (WP ((e.subst f (.rec_ f x e)).subst x v) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.app (Exp.val (Val.rec_ f x e)) (Exp.val v)) @ m ; ⊤ {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_4, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, Val.rec!, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_cont
  simp_all only [wp_unfold]
  iexact H0_1

theorem wp_rec {M : CoPset} (f x : Binder) (e : Exp) (Φ : Val → IProp GF) :
    m (Φ (.rec_ f x e)) -∗
    WP (Exp.rec_ f x e) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_3]
  iintro H0_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_pair {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ (.pair v₁ v₂)) -∗
    WP (Exp.pair (.val v₁) (.val v₂)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_8, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_fst {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ v₁) -∗
    WP (Exp.fst (.val (.pair v₁ v₂))) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_9, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, Val.pair!, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_snd {M : CoPset} (v₁ v₂ : Val) (Φ : Val → IProp GF) :
    m (Φ v₂) -∗
    WP (Exp.snd (.val (.pair v₁ v₂))) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_10, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, Val.pair!, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_injL {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    m (Φ (.injL v)) -∗
    WP (Exp.injL (.val v)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_11, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_injR {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    m (Φ (.injR v)) -∗
    WP (Exp.injR (.val v)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_12, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iexact H0_1

theorem wp_caseL (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP (Exp.app e₁ (Exp.val v)) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injL v)) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [val_to_ofVal, ↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_cont
  simp_all only [wp_unfold]
  iexact H0_1

theorem wp_caseR (v : Val) (e₁ e₂ : Exp) (Φ : Val → IProp GF) :
    m (WP (Exp.app e₂ (Exp.val v)) @ m ; ⊤ {{ Φ }}) -∗
    WP (Exp.case (Exp.val (Val.injR v)) e₁ e₂) @ m ; ⊤ {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_13, Exp.isVal, Exp.denote.eq_1]
  iintro H0_1
  simp_all only [val_to_ofVal, ↓reduceIte, pure_bind]
  iapply IrisITreeScript.HeapLang.wpi_cont
  simp_all only [wp_unfold]
  iexact H0_1

theorem wp_fork (e : Exp) (Φ : Val → IProp GF) :
    m (Φ (.lit .unit)) -∗
    WP e @ m; ⊤ {{ v, ⌜v = .lit .unit⌝ }} -∗
    WP (Exp.fork e) @ m; ⊤ {{ Φ }} := by
  iintro HΦ Hwp
  simp only [wp_unfold, Exp.denote.eq_21, Exp.isVal]
  iapply wpi_bind; iapply wpi_fork $$ [HΦ]
  · iapply IrisITreeScript.HeapLang.wpi_step_pure
    iexact HΦ
  · iapply wpi_bind;
    cases e <;> simp only [↓reduceIte, ConcE.yieldAfter, Bool.false_eq_true]
    · simp_all only [val_to_ofVal]
      iapply IrisITreeScript.HeapLang.wp_val
      iapply IrisITreeScript.Core.wpi_pure
      (ipureintro; simp)
    all_goals
      iapply wpi_bind; iapply wpi_wand $$ Hwp
      iintro %r
      iintro H0_1
      icases H0_1 with %H0_2
      rw [H0_2]
      iapply IrisITreeScript.Core.wpi_bind
      iapply IrisITreeScript.Effects.wpi_yield
      iapply IrisITreeScript.Core.wpi_pure
      iapply IrisITreeScript.Core.wpi_pure
      (ipureintro; try simp)

section heap_rules

attribute [local simp] Val.int!
/- [Note]: Remove this theorem from the simp set. -/
attribute [-simp] Int.not_le

@[ibubble 75%]
theorem wp_allocN {M : CoPset} (n : Int) (v : Val) (Φ : Val → IProp GF) :
    0 < n →
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    m iprop(∀ l : Loc,
      ([∗list] i ∈ List.range n.toNat, (l + Int.ofNat i) ↦ v) -∗
      Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int n))) (.val v)) @ m; M {{ Φ }} := by
  iintro %Hpos %Hmask HΦ
  have Hle := Int.not_le.mpr Hpos; clear Hpos
  simp only [wp_unfold, Exp.denote.eq_14, Exp.isVal, Exp.denote.eq_1]
  simp_all only [Int.ofNat_eq_natCast, ↓reduceIte, Val.int!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_allocN
  simp [*]
  iintro %l
  iintro H2_1
  simp_all only [Int.ofNat_eq_natCast]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ HΦ ]
  iexact HΦ
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_alloc {M : CoPset} (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    m iprop(∀ l, l ↦ v -∗ Φ (.lit (.loc l))) -∗
    WP (Exp.allocN (.val (.lit (.int 1))) (.val v)) @ m; M {{ Φ }} := by
  iintro %x
  iintro H0_1
  simp_all only [val_to_ofVal, wp_unfold]
  iapply IrisITreeScript.HeapLang.wp_allocN
  simp [*]
  simp [*]
  simp_all only [Int.ofNat_eq_natCast, Int.toNat_one, List.range_one, Algebra.BigOpL.bigOpL_cons,
    Int.cast_ofNat_Int, LawfulLoc.add_zero, Algebra.BigOpL.bigOpL_nil]
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_1 ]
  iexact H0_1
  iintro H2_1
  iintro %l
  iintro H2_2
  icases H2_2 with ⟨H2_3, H2_4⟩
  icases H2_4 with #H2_5
  iapply H2_1
  iexact H2_3

theorem wp_load {M : CoPset} (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦{dq} v -∗
    m iprop(l ↦{dq} v -∗ Φ v) -∗
    WP (Exp.load (Exp.val (Val.lit (BaseLit.loc l)))) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_16, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro H0_1
  iintro H0_2
  simp_all only [↓reduceIte, Val.loc!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_load! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_store {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦ v' -∗ Φ (.lit .unit)) -∗
    WP (Exp.store (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_17, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro H0_1
  iintro H0_2
  simp_all only [↓reduceIte, Val.loc!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_store! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_free {M : CoPset} (l : Loc) (v : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦? (none : Option Val) -∗ Φ (.lit .unit)) -∗
    WP (Exp.free (Exp.val (Val.lit (BaseLit.loc l)))) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_15, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro H0_1
  iintro H0_2
  simp_all only [↓reduceIte, Val.loc!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_storeOpt $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  simp_all only
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_xchg {M : CoPset} (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ v -∗
    m iprop(l ↦ v' -∗ Φ v) -∗
    WP (Exp.xchg (Exp.val (Val.lit (BaseLit.loc l))) (Exp.val v')) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_19, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro H0_1
  iintro H0_2
  simp_all only [↓reduceIte, Val.loc!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_store! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_cmpXchg_fail {M : CoPset} (l : Loc) (dq : DFrac) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' ≠ v₁ →
    v'.compareSafe v₁ = true →
    l ↦{dq} v' -∗
    m iprop(l ↦{dq} v' -∗ Φ (.pair v' (.lit (.bool false)))) -∗
    WP (Exp.cmpXchg (Exp.val $ Val.lit $ BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_18, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  iintro H0_2
  simp_all only [ne_eq, ↓reduceIte, Val.loc!, Bool.not_eq_eq_eq_not, Bool.not_true, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_load! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  rw [h0_2]
  simp_all only
  simp_all only [Bool.true_eq_false, ↓reduceIte]
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H4_1
  iapply H4_1
  iexact H2_1

theorem wp_cmpXchg_suc {M : CoPset} (l : Loc) (v' v₁ v₂ : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    v' = v₁ →
    v'.compareSafe v₁ = true →
    l ↦ v' -∗
    m iprop(l ↦ v₂ -∗ Φ (.pair v' (.lit $ .bool true))) -∗
    WP (Exp.cmpXchg (Exp.val $ Val.lit $ BaseLit.loc l) (Exp.val v₁) (Exp.val v₂))
      @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_18, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro %h0_1
  iintro %h0_2
  iintro H0_1
  iintro H0_2
  rw [h0_1]
  simp_all only
  simp_all only [↓reduceIte, Val.loc!, Bool.not_eq_eq_eq_not, Bool.not_true, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_load! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  rw [h0_2]
  simp_all only
  simp_all only [Bool.true_eq_false, ↓reduceIte]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_store! $$ [ H2_1 ]
  simp [*]
  iexact H2_1
  iintro H4_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H6_1
  iapply H6_1
  iexact H4_1

theorem wp_faa {M : CoPset} (l : Loc) (i₁ i₂ : Int) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (GF := GF) (Loc := Loc) (Val := Val)) ⊆ M →
    l ↦ Val.lit (.int i₁) -∗
    m iprop(l ↦ (.lit (.int (i₁ + i₂)) : Val) -∗ Φ (.lit (.int i₁))) -∗
    WP (Exp.faa (.val $ .lit $ .loc l) (.val $ .lit $ .int i₂)) @ m ; M {{ Φ }} := by
  simp only [wp_unfold, Exp.denote.eq_20, Exp.isVal, Exp.denote.eq_1]
  iintro %x
  iintro H0_1
  iintro H0_2
  simp_all only [↓reduceIte, Val.loc!, Val.int!, pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_load! $$ [ H0_1 ]
  simp [*]
  iexact H0_1
  iintro H2_1
  simp_all only
  simp_all only [pure_bind]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_store! $$ [ H2_1 ]
  simp [*]
  iexact H2_1
  iintro H4_1
  iapply IrisITreeScript.HeapLang.wpi_step_pure
  iapply IrisITreeScript.Effects.StepMod.map $$ [ H0_2 ]
  iexact H0_2
  iintro H6_1
  iapply H6_1
  iexact H4_1

end heap_rules

end wp_rules
