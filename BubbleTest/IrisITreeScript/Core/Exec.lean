module

import Bubble

public import BubbleTest.IrisITreeScript.Core.Handler
public import BubbleTest.IrisITreeScript.Core.Wpi
public import Iris.ProofMode
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.BigOp.BigSepList
public import ITree.Definition
public import ITree.Exec

@[expose] public section

namespace IrisITreeScript.Core

open Iris BI ITree Std OFE

def bi_close {PROP : Type _} [BI PROP] {α : Type _} (R : α → α → Prop) (P : α → PROP) : α → PROP :=
  λ a => iprop(∃ a', ⌜R a a'⌝ ∗ P a')

section bi_close

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type} (R : α → α → Prop)

attribute [local simp] bi_close

theorem bi_close_mono (P1 P2 : α → PROP) (a : α) :
    bi_close R P1 a ⊢ (∀ y, P1 y -∗ P2 y) -∗ bi_close R P2 a := by
  iintro H0_1
  iintro H0_2
  simp_all only [bi_close]
  icases H0_1 with ⟨%h0_1, H0_3⟩
  icases H0_3 with ⟨H0_4, H0_5⟩
  icases H0_4 with %H0_6
  iexists _
  isplit
  (ipureintro; assumption)
  iapply H0_2
  iexact H0_5

theorem bi_close_intro (P : α → PROP) (a : α) [Href : Std.Refl R] :
    P a ⊢ bi_close R P a := by
  iintro H0_1
  simp_all only [bi_close]
  iexists _
  isplit
  pick_goal 2
  iexact H0_1
  (ipureintro; exact Href.refl _)

theorem bi_close_respect (P : α → PROP) [Hsym : Symm R] [Htran : Trans R R R] :
    ∀ {x y : α}, R x y → bi_close R P x ⊣⊢ bi_close R P y := by
  iintro %x
  iintro %h0_1
  iintro %h0_2
  simp_all only [bi_close]
  isplit
  iintro H1_1
  icases H1_1 with ⟨%h1_1, H1_2⟩
  icases H1_2 with ⟨H1_3, H1_4⟩
  icases H1_3 with %H1_5
  iexists _
  isplit
  pick_goal 2
  iexact H1_4
  ipureintro
  rotate_left
  iintro H1_1
  icases H1_1 with ⟨%h1_1, H1_2⟩
  icases H1_2 with ⟨H1_3, H1_4⟩
  icases H1_3 with %H1_5
  iexists _
  isplit
  pick_goal 2
  iexact H1_4
  ipureintro
  rotate_left
  · exact Htran.trans (Hsym.symm _ _ h0_2) H1_5
  · exact Htran.trans h0_2 H1_5

end bi_close

/-- [bi_mono0] : linear monotone closure of a predicate transformer. -/
def bi_mono0 {PROP : Type _} [BI PROP] {α : Type _} (P : (α → PROP) → PROP) : (α → PROP) → PROP :=
  λ Q => iprop(∃ Q' : α → PROP, P Q' ∗ ∀ x, Q' x -∗ Q x)

section bi_mono0

variable {PROP : Type _} [BI PROP] {α : Type _}

attribute [local simp] bi_mono0

theorem bi_mono0_intro0 (P : (α → PROP) → PROP) (Q : α → PROP) :
    P Q ⊢ bi_mono0 P Q := by
  iintro H0_1
  simp_all only [bi_mono0]
  iexists _
  isplitl [H0_1]
  pick_goal 2
  iintro %x
  iintro H2_1
  iexact H2_1
  iexact H0_1

@[ibubble 50%]
theorem bi_mono0_mono (P : (α → PROP) → PROP) (Q1 Q2 : α → PROP) :
    bi_mono0 P Q1 ⊢ (∀ x, Q1 x -∗ Q2 x) -∗ bi_mono0 P Q2 := by
  iintro H0_1
  iintro H0_2
  simp_all only [bi_mono0]
  icases H0_1 with ⟨%h0_1, H0_3⟩
  icases H0_3 with ⟨H0_4, H0_5⟩
  iexists _
  isplitl [H0_4]
  iexact H0_4
  iintro %x
  iintro H2_1
  iapply H0_2
  iapply H0_5
  iexact H2_1

theorem bi_mono0_mono_l (P1 P2 : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P1 Q ⊢ (∀ Q, P1 Q -∗ P2 Q) -∗ bi_mono0 P2 Q := by
  iintro H0_1
  iintro H0_2
  simp_all only [bi_mono0]
  icases H0_1 with ⟨%h0_1, H0_3⟩
  icases H0_3 with ⟨H0_4, H0_5⟩
  iexists _
  isplitl [H0_4 H0_2]
  pick_goal 2
  iintro %x
  iintro H2_1
  iapply H0_5
  iexact H2_1
  iapply H0_2
  iexact H0_4

theorem bi_mono0_elim (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 P Q ⊢ (∀ Q Q', (∀ x, Q' x -∗ Q x) -∗ P Q' -∗ P Q) -∗ P Q := by
  iintro H0_1
  iintro H0_2
  simp_all only [bi_mono0]
  icases H0_1 with ⟨%h0_1, H0_3⟩
  icases H0_3 with ⟨H0_4, H0_5⟩
  iapply H0_2 $$ [ H0_5 ] [ H0_4 ]
  pick_goal 2
  iexact H0_4
  iintro %x
  iintro H1_1
  iapply H0_5
  iexact H1_1

theorem bi_mono0_dup (P : (α → PROP) → PROP) (Q : α → PROP) :
    bi_mono0 (bi_mono0 P) Q ⊢ bi_mono0 P Q := by
  iintro H0_1
  simp_all only [bi_mono0]
  icases H0_1 with ⟨%h0_1, H0_2⟩
  icases H0_2 with ⟨H0_3, H0_4⟩
  icases H0_3 with ⟨%h0_1, H0_5⟩
  icases H0_5 with ⟨H0_6, H0_7⟩
  iexists _
  isplitl [H0_6]
  iexact H0_6
  iintro %x
  iintro H2_1
  iapply H0_4
  iapply H0_7
  iexact H2_1

theorem bi_mono0_intro (P : (α → PROP) → PROP) (Q Q' : α → PROP) :
    P Q' ⊢ (∀ x, Q' x -∗ Q x) -∗ bi_mono0 P Q := by
  iintro H0_1
  iintro H0_2
  simp_all only [bi_mono0]
  iexists _
  isplitl [H0_1]
  iexact H0_1
  iintro %x
  iintro H2_1
  iapply H0_2
  iexact H2_1

end bi_mono0

/-- The functional whose least fixed point is `lfp_tp`. -/
def lfp_tpF {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (rec_tp : DiscreteO (List ((α → PROP) → PROP)) → PROP) :
    DiscreteO (List ((α → PROP) → PROP)) → PROP :=
  λ Ms => iprop(
    ∀ (i : Nat) (M : (α → PROP) → PROP), ⌜Ms.car[i]? = some M⌝ -∗
      bi_mono0 M λ x => iprop(
        ∃ G, F G x ∗ ∀ Ms', ([∗list] M' ∈ Ms', M' G) -∗ rec_tp ⟨Ms' ++ Ms.car.eraseIdx i⟩
      )
  )

section lfp_tp

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

instance lfp_tpF_ne : NonExpansive (lfp_tpF F) where
  ne {_ _ _} Hfg := by
    intro Ms; unfold lfp_tpF bi_mono0
    refine forall_ne λ i => forall_ne λ _ => ?_
    refine wand_ne.ne .rfl $ exists_ne λ _ => ?_
    refine sep_ne.ne .rfl $ forall_ne λ _ => ?_
    refine wand_ne.ne .rfl $ exists_ne λ _ => ?_
    refine sep_ne.ne .rfl $ forall_ne λ Ms' => ?_
    exact wand_ne.ne .rfl $ Hfg ⟨Ms' ++ Ms.car.eraseIdx i⟩

@[ibubble 70%]
theorem lfp_tpF_mono (tp1 tp2 : DiscreteO (List ((α → PROP) → PROP)) → PROP) :
    ⊢ □ (∀ Ms, tp1 Ms -∗ tp2 Ms) -∗
      ∀ Ms, lfp_tpF F tp1 Ms -∗ lfp_tpF F tp2 Ms := by
  iintro #Hwand %Ms Htp; unfold lfp_tpF
  iintro %i %M %Hi
  ispecialize Htp $$ %i %M %Hi
  iapply IrisITreeScript.Core.bi_mono0_mono $$ [ Htp ]
  iexact Htp
  iintro %x
  iintro H1_1
  icases H1_1 with ⟨%h1_1, H1_2⟩
  icases H1_2 with ⟨H1_3, H1_4⟩
  iexists _
  isplitl [H1_3]
  iexact H1_3
  iintro %Ms'
  iintro H3_1
  iapply Hwand
  iapply H1_4
  iexact H3_1

instance : BIMonoPred (lfp_tpF (PROP := PROP) F) where
  mono_pred := by
    iintro %x
    iintro %h0_1
    iintro %h0_2
    iintro %h0_3
    iintro H0_1
    iintro %h0_4
    iintro H0_2
    icases H0_1 with #H0_3
    iapply IrisITreeScript.Core.lfp_tpF_mono $$ [ ]
    pick_goal 2
    iexact H0_2
    iintro !>
    iintro %Ms
    iintro H1_1
    iapply H0_3
    iexact H1_1

  mono_pred_ne.ne n Φ Φ' Hdist := by
    cases Hdist; rfl

end lfp_tp

/-- The `lfp_tp` least-fixed-point predicate. -/
def lfp_tp {PROP : Type _} [BI PROP] {α : Type _}
    (F : (α → PROP) → (α → PROP))
    (Ms : List ((α → PROP) → PROP)) : PROP :=
  bi_least_fixpoint (lfp_tpF F) ⟨Ms⟩

section lfp_tp_lemmas

variable {PROP : Type _} [BI PROP] [BIAffine PROP] {α : Type _}
  (F : (α → PROP) → (α → PROP))

attribute [local simp] bi_close lfp_tp

@[ibubble 75%]
theorem lfp_tp_unfold (Ms : List ((α → PROP) → PROP)) :
    lfp_tp F Ms ⊣⊢ lfp_tpF F (λ Ms => lfp_tp F Ms.car) ⟨Ms⟩ :=
  equiv_iff.mp <| least_fixpoint_unfold (lfp_tpF F)

@[ibubble 75%]
theorem lfp_tp_nil : ⊢ (lfp_tp F [] : PROP) := by
  iapply (lfp_tp_unfold F []).mpr
  simp only [lfp_tpF]
  iintro %i
  iintro %M
  iintro H0_1
  icases H0_1 with %H0_2
  simp_all only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg,
    not_none_eqv_some]

theorem lfp_tp_ind (Φ : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    [NonExpansive Φ] :
    ⊢ □ (∀ y, lfp_tpF F (λ x => iprop(Φ x ∧ lfp_tp F x.car)) y -∗ Φ y) -∗
      (∀ Ms, lfp_tp F Ms.car -∗ Φ Ms) := by
  iintro #Hwand %Ms Hlfp
  iapply least_fixpoint_ind (lfp_tpF F)
  · iintro !>
    iintro %y
    iintro H0_1
    simp_all only [lfp_tp]
    iapply Hwand
    iexact H0_1
  · simp_all only [lfp_tp]
    iexact Hlfp

attribute [-simp] lfp_tp

-- Helper function for [lfp_*_perm_*]
theorem perm_pick_erase {β : Type _} {Ms1 Ms2 : List β} {i : Nat} {M : β}
    (hperm : Ms1.Perm Ms2) (Hi : Ms2[i]? = some M) :
    ∃ j, Ms1[j]? = some M ∧ (Ms1.eraseIdx j).Perm (Ms2.eraseIdx i) := by
  induction hperm generalizing i M with
  | nil => simp at Hi
  | cons x hperm ih => cases i with
    | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simpa
    | succ i =>
      simp at Hi; rcases ih Hi with ⟨j, Hj, Hperm⟩
      refine ⟨j + 1, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Hj
      · simpa [List.eraseIdx_cons_succ] using List.Perm.cons x Hperm
  | swap x y l => cases i with
    | zero => simp at Hi; subst M; refine ⟨1, ?_, ?_⟩; simp; simp
    | succ i => cases i with
      | zero => simp at Hi; subst M; refine ⟨0, ?_, ?_⟩; simp; simp
      | succ i =>
        simp at Hi; refine ⟨i + 2, ?_, ?_⟩
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hi
        · simpa [List.eraseIdx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using List.Perm.swap x y (l.eraseIdx i)
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₂ Hi with ⟨j₂, Hj₂, Hperm₂⟩
      rcases ih₁ Hj₂ with ⟨j₁, Hj₁, Hperm₁⟩
      exact ⟨j₁, Hj₁, List.Perm.trans Hperm₁ Hperm₂⟩

@[ibubble 50%]
theorem lfp_tpF_perm (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp1 wp2 : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp1 ⟨Ms1⟩ ⊢
    (∀ (Ns1 Ns2 : DiscreteO (List ((α → PROP) → PROP))),
      ⌜Ns1.car.Perm Ns2.car⌝ -∗ wp1 Ns1 -∗ wp2 Ns2) -∗
    lfp_tpF F wp2 ⟨Ms2⟩ := by
  iintro Htp Hwp; unfold lfp_tpF; iintro %i %M %Hi
  rcases perm_pick_erase h Hi with ⟨j, Hj, Herase⟩
  simp_all only
  iapply IrisITreeScript.Core.bi_mono0_mono $$ [ Htp ]
  iapply Htp
  rw [Hj]
  simp_all only
  ipureintro
  rotate_left
  iintro %x
  iintro H1_1
  icases H1_1 with ⟨%h1_1, H1_2⟩
  icases H1_2 with ⟨H1_3, H1_4⟩
  iexists _
  isplitl [H1_3]
  iexact H1_3
  iintro %Ms'
  iintro H3_1
  iapply Hwp $$ [ ] [ H3_1 H1_4 ]
  pick_goal 2
  iapply H1_4
  iexact H3_1
  simp_all only
  ipureintro
  rotate_left
  · simp
  · exact (List.perm_append_left_iff Ms').2 Herase

theorem lfp_tpF_perm_close (Ms1 Ms2 : List ((α → PROP) → PROP))
    (wp : DiscreteO (List ((α → PROP) → PROP)) → PROP)
    (h : Ms1.Perm Ms2) :
    lfp_tpF F wp ⟨Ms1⟩ ⊢
    lfp_tpF F (bi_close (λ a b => a.car.Perm b.car) wp) ⟨Ms2⟩ := by
  iintro H0_1
  iapply IrisITreeScript.Core.lfp_tpF_perm $$ [ H0_1 ]
  pick_goal 2
  iexact H0_1
  rotate_left
  iintro %Ns1
  iintro %Ns2
  iintro H1_1
  iintro H1_2
  icases H1_1 with %H1_3
  simp_all only [bi_close]
  iexists _
  isplit
  pick_goal 2
  iexact H1_2
  ipureintro
  rotate_left
  · exact h
  · exact H1_3.symm

theorem lfp_tp_perm (Ms1 Ms2 : List ((α → PROP) → PROP)) (h : Ms1.Perm Ms2) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 := by
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) := ⟨
      λ n lst1 lst2 Hlst => by
        refine forall_ne (λ lst => ?_)
        cases Hlst; rfl
    ⟩
  iintro Htp; irevert %Ms2 %h
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, ⌜Ms.car.Perm Ms2⌝ -∗ lfp_tp F Ms2) $$ [] Htp
  iintro !>
  iintro %y
  iintro H0_1
  iintro %Ms2
  iintro H0_2
  icases H0_2 with %H0_3
  iapply IrisITreeScript.Core.lfp_tp_unfold
  iapply IrisITreeScript.Core.lfp_tpF_mono $$ [ ]
  pick_goal 2
  iapply IrisITreeScript.Core.lfp_tpF_perm $$ [ H0_1 ]
  assumption
  iexact H0_1
  iintro %Ns1
  iintro %Ns2
  iintro H3_1
  iintro H3_2
  icases H3_1 with %H3_3
  iapply H3_2
  (ipureintro; assumption)
  iintro !>
  iintro %Ms
  iintro H2_1
  iexact H2_1

theorem lfp_tp_app (Ms1 Ms2 : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F Ms1 -∗ lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2) := by
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2)) := ⟨
      λ n ls1 lst2 Hlst => by
        refine forall_ne (λ Ms2 => ?_)
        cases Hlst; rfl
    ⟩
  letI : NonExpansive λ (Ms : DiscreteO (List ((α → PROP) → PROP))) =>
    iprop(∀ Ms1, lfp_tpF F (λ x => iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms))
      ∧ lfp_tp F x.car)) Ms1 -∗ lfp_tp F (Ms1.car ++ Ms.car)) := ⟨
        λ n lst1 lst2 Hlst => by
          refine forall_ne (λ Ms1 => ?_)
          cases Hlst; rfl
      ⟩
  have Hwrap : ⊢ (∀ (Ms1 : DiscreteO (List ((α → PROP) → PROP))),
    iprop(lfp_tp F Ms1.car -∗ ∀ Ms2, iprop(lfp_tp F Ms2 -∗
      lfp_tp F (Ms1.car ++ Ms2)))) -∗
    ∀ (Ms1 : List ((α → PROP) → PROP)), iprop(lfp_tp F Ms1 -∗
      ∀ Ms2, iprop(lfp_tp F Ms2 -∗ lfp_tp F (Ms1 ++ Ms2))) := by
    iintro H %Ms1 Hx1 %Ms2 Hx2
    iapply H $$ %⟨Ms1⟩ Hx1 %Ms2 Hx2
  have Hwrap2 : ⊢ (∀ (Ms2 : DiscreteO (List ((α → PROP) → PROP))),
    iprop(lfp_tp F Ms2.car -∗ ∀ Ms1, iprop(lfp_tpF F (λ x =>
      iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
      lfp_tp F (Ms1.car ++ Ms2.car)))) -∗
    ∀ (Ms2 : List ((α → PROP) → PROP)), iprop(lfp_tp F Ms2 -∗ BI.forall (λ Ms1 =>
      iprop(lfp_tpF F (λ x => iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧
      lfp_tp F x.car)) Ms1 -∗ lfp_tp F (Ms1.car ++ Ms2)))) := by
    iintro H %Ms2 Hx2 %Ms1 Hx1
    iapply H $$ %⟨Ms2⟩ Hx2 %Ms1 Hx1
  iintro Hx1 Hx2; irevert %Ms1 Hx1 %Ms2 Hx2; iapply Hwrap; iclear %Hwrap
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms2, lfp_tp F Ms2 -∗ lfp_tp F (Ms.car ++ Ms2))
  iintro !> %Ms1 Hx1 %Ms2 Hx2; irevert %Ms2 Hx2 %Ms1 Hx1; iapply Hwrap2; iclear %Hwrap2
  iapply lfp_tp_ind F λ Ms => iprop(∀ Ms1, lfp_tpF F (λ x =>
    iprop((∀ Ms, lfp_tp F Ms -∗ lfp_tp F (x.car ++ Ms)) ∧ lfp_tp F x.car)) Ms1 -∗
      lfp_tp F (Ms1.car ++ Ms.car))
  repeat clear this
  iintro !> %Ms2 Hx2 %Ms1 Hx1; iapply lfp_tp_unfold; unfold lfp_tpF at ⊢; simp
  iintro %i %M %Hlookup
  by_cases Hi : i < Ms1.car.length
  · -- M appears in Ms1
    have Hloc := List.getElem?_append_left Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_lt_length Hi Ms2.car]
    ispecialize Hx1 $$ %i %M %Hloc; iapply bi_mono0_mono $$ Hx1
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩
    iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩; iapply Happend
    iapply (lfp_tp_unfold F Ms2.car).mpr; simp only [lfp_tpF]
    iintro %j %N %Hj; ispecialize Hx2 $$ %j %N %Hj
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    iapply Hcont
  · -- M appears in Ms2
    have Hi := Nat.le_of_not_gt Hi
    have Hloc := List.getElem?_append_right Hi ▸ Hlookup
    rw [List.eraseIdx_append_of_length_le Hi Ms2.car]
    ispecialize Hx2 $$ %(i - Ms1.car.length) %M %Hloc
    iapply bi_mono0_mono $$ Hx2
    iintro %x ⟨%G, ⟨HF, Hcont⟩⟩; iexists G; iframe
    iintro %Ms' HMs'; ispecialize Hcont $$ %Ms' HMs'
    icases Hcont with ⟨Happend, -⟩
    ispecialize Happend $$ %Ms1 Hx1
    iapply lfp_tp_perm F _ _ _ $$ Happend
    exact List.perm_append_comm_assoc _ _ _

@[local ibubble 75%]
theorem lfp_tp_cons (M : (α → PROP) → PROP) (Ms : List ((α → PROP) → PROP)) :
    ⊢ lfp_tp F [M] -∗ lfp_tp F Ms -∗ lfp_tp F (M :: Ms) := by
  simpa using (lfp_tp_app F [M] Ms)

@[local ibubble 75%]
theorem lfp_tp_singleton_mod_elim (M : (α → PROP) → PROP) :
    ⊢ M (λ x => lfp_tp F [λ P => P x]) -∗ lfp_tp F [M] := by
  iintro Hx; iapply lfp_tp_unfold; simp only [lfp_tpF]
  iintro %i %M' %Hi; cases i with
  | zero =>
    simp at Hi; subst M'; simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro M $$ Hx; iintro %x Hlfp;
    ihave Hlfp := lfp_tp_unfold F [λ P => P x] $$ Hlfp; simp only [lfp_tpF];
    have Hlookup : ([λ P => P x] : List ((α → PROP) → PROP))[0]? = some (λ P => P x) := by simp
    ispecialize Hlfp $$ %0 %(λ P => P x) %Hlookup
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_elim $$ Hlfp;
    iintro %Q
    iintro %Q'
    iintro H0_1
    iintro H0_2
    simp_all only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
      List.getElem_cons_zero]
    iapply H0_1
    iexact H0_2
  | succ n => simp at Hi

variable {α : Type _} [OFE α] [OFE.Discrete α]

theorem lfp_tp_intro (G : (α → PROP) → (α → PROP)) (x : α) :
    ⊢ bi_least_fixpoint G x -∗ lfp_tp G [λ P => P x] := by
  letI : NonExpansive (fun (x : α) => lfp_tp G [λ P => P x] : α → PROP) := ⟨
    fun {n x1 x2} Hx => by
      have Heq : x1 = x2 := OFE.Discrete.discrete Hx
      subst Heq; rfl
  ⟩
  have Hlist : ∀ Ms : List ((α → PROP) → PROP),
      ⊢ ([∗list] M ∈ Ms, M (λ x => lfp_tp G [λ P => P x])) -∗ lfp_tp G Ms := by
    intro Ms
    iinduction Ms with
    | nil => iintro H0_1
             icases H0_1 with #H0_2
             simp_all only [Algebra.BigOpL.bigOpL_nil]
             iapply IrisITreeScript.Core.lfp_tp_nil
    | cons M Ms ih =>
      iintro HMs; ihave HMs := BigSepL.bigSepL_cons.mp $$ HMs
      icases HMs with ⟨H0_1, H0_2⟩
      iapply IrisITreeScript.Core.lfp_tp_cons $$ [ H0_1 ]
      iapply IrisITreeScript.Core.lfp_tp_singleton_mod_elim
      iexact H0_1
      iapply ih
      iexact H0_2
  iintro Hlfp; irevert %x Hlfp
  iapply least_fixpoint_iter
  clear this
  iintro !> %x HF; iapply lfp_tp_unfold
  simp only [lfp_tpF]
  iintro %i %M %Hi
  cases i with
  | zero =>
    simp at Hi; subst M
    simp only [List.eraseIdx, List.append_nil]
    iapply bi_mono0_intro0; simp only []
    iexists _; isplitl [HF]
    · iassumption
    · iintro %Ms HMs
      iinduction Ms with
      | nil => icases HMs with #H0_1
               simp_all only [Algebra.BigOpL.bigOpL_nil]
               iapply IrisITreeScript.Core.lfp_tp_nil
      | cons M Ms IHM =>
        simp_all only [Algebra.BigOpL.bigOpL_cons]
        icases HMs with ⟨H0_1, H0_2⟩
        iapply IrisITreeScript.Core.lfp_tp_cons $$ [ H0_1 ]
        iapply IrisITreeScript.Core.lfp_tp_singleton_mod_elim
        iexact H0_1
        iapply Hlist
        iexact H0_2
  | succ i => simp at Hi

end lfp_tp_lemmas

end IrisITreeScript.Core
