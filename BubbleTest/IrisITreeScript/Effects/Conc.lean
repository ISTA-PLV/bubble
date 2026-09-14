module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITreeScript.Core.Wpi
public import ITree.Effects.Conc

@[expose] public section

namespace IrisITreeScript.Effects

open Iris Iris.BI ITree ITree.Effects IrisITreeScript.Core

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def concH : IHandler PROP concE where
  ihandle
    | .fork, Φ, Φs => iprop(Φ .parent ∗ |={⊤, ∅}=> Φs .child)
    | .yield, Φ, _ => iprop(|={∅, ⊤}=> |={⊤, ∅}=> Φ ⟨⟩)
    | .kill, _, _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %Φs %Φs' HΦwand #Hswand HH
    cases i
    · simp_all only
      icases HH with ⟨H0_1, H0_2⟩
      isplitl [H0_1 HΦwand]
      iapply HΦwand
      iexact H0_1
      iapply Hswand
      iexact H0_2
    · simp_all only
      iexact HH
    · simp_all only
      iapply HΦwand
      iexact HH

end handler

section wpi_rules

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]
  {E : Effect} {H : IHandler PROP E}
  [concE -< E] [Hin : InH concH H]

attribute [local ibubble 50%] fupd_mask_intro
attribute [local simp] concH

@[ibubble 75%]
theorem wpi_kill M (Φ : PUnit → PROP) :
    True -∗ WPi kill @> H; ⊤, M {{Φ}} := by
  unfold kill
  iintro H0_1
  simp_all only [concH]
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Core.wpi_trigger
  icases H0_1 with %H2_1
  simp_all only
  iapply Iris.fupd_mask_intro
  simp
  iintro H3_1
  imod H3_1 with H3_1
  icases H3_1 with #H4_1
  (ipureintro; simp)

@[ibubble 75%]
theorem wpi_fork M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, iprop(True) }} -∗
    WPi fork t @> H; M {{Φ}} := by
  unfold fork
  iintro HΦ Ht; iapply wpi_trigger_bind; simp [concH]
  iapply fupd_mask_intro (by simp); iintro Hm
  isplitr [Ht]
  · simp_all only [concH]
    imod Hm with Hm
    icases Hm with #H1_1
    iapply IrisITreeScript.Core.wpi_pure
    iexact HΦ
  · simp_all only [concH]
    iapply Iris.fupd_mask_intro
    simp
    iintro H1_1
    imod H1_1 with H1_1
    icases H1_1 with #H2_1
    iapply IrisITreeScript.Core.wpi_bind
    iapply IrisITreeScript.Core.wpi_wand $$ [ Ht ]
    iexact Ht
    iintro %r
    iintro H4_1
    iapply IrisITreeScript.Effects.wpi_kill
    icases H4_1 with %H5_1
    simp_all only
    (ipureintro; simp)

@[ibubble 75%]
theorem wpi_yield (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi yield @> H; ⊤ {{Φ}} := by
  unfold yield
  iintro H0_1
  simp_all only [concH]
  iapply IrisITreeScript.Core.wpi_trigger
  simp_all only
  iapply Iris.fupd_mask_intro
  simp
  iintro H2_1
  imod H2_1 with H2_1
  icases H2_1 with #H3_1
  imodintro
  iapply Iris.fupd_mask_intro
  simp
  iintro H5_1
  imod H5_1 with H5_1
  icases H5_1 with #H6_1
  imodintro
  iexact H0_1

end wpi_rules

section exec

open ITree.Exec IrisITreeScript.Core

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP] [BIAffine PROP]

private theorem filterMap_set_perm {T U : Type _} (f : T → U)
    (xs : List (Option T)) (i : Nat) (old new : Option T)
    (hi : i < xs.length) (hx : xs[i] = old) :
    ((old.map f).toList ++ (xs.set i new).filterMap (Option.map f)).Perm
      ((new.map f).toList ++ xs.filterMap (Option.map f)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih => cases i with
    | zero =>
      simp at hx; subst a
      cases old <;> cases new <;> simp
      exact .swap _ _ _
    | succ i =>
      simp at hi hx ⊢; have hp := ih i hi hx
      cases a with
      | none => exact hp
      | some y =>
        cases old <;> cases new <;> simp at hp ⊢
        · exact hp
        · exact (List.Perm.cons (f y) hp).trans (List.Perm.swap _ _ _)
        · exact (List.Perm.swap _ _ _).trans (List.Perm.cons (f y) hp)
        · exact (List.Perm.swap _ _ _).trans ((List.Perm.cons (f y) hp).trans (List.Perm.swap _ _ _))

instance coneEH_adequate {GE GR} :
    EHandlerAdequate (PROP:=PROP) concH (concEH (GE:=GE) (GR:=GR)) where
  inv s Ms :=
    iprop(<affine> ⌜Ms = s.pool.filterMap λ t =>
      (λ t P => iprop(|={⊤, ∅}=> P t)) <$> t⌝)
  adequate := by
    intro G i s Ms C k Hhandle
    simp [concH, concEH] at Hhandle ⊢
    cases i <;> simp at Hhandle ⊢
    · -- Fork case
      iintro ⟨Hparent, Hchild⟩ %h !>
      iexists _, _, λ P => P (k .parent),
        Ms ++ [(λ P => iprop(|={⊤, ∅}=> P (k .child)))],
        [λ P => P (k .parent), λ P => iprop(|={⊤, ∅}=> P (k .child))]
      rw [h]
      simp_all only
      simp_all only [List.cons_append, List.nil_append, List.perm_cons, List.perm_append_singleton,
        Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
      isplit
      pick_goal 2
      isplit
      ipureintro
      pick_goal 2
      isplitl [Hparent Hchild]
      isplitl [Hparent]
      iexact Hparent
      isplit
      iexact Hchild
      ipureintro
      pick_goal 2
      isplit
      ipureintro
      pick_goal 3
      iintro %P
      iintro H4_1
      imodintro
      iexact H4_1
      pick_goal 8
      ipureintro
      pick_goal 10
      pick_goal 10
      pick_goal 9
      pick_goal 8
      pick_goal 8
      pick_goal 7
      pick_goal 7
      pick_goal 8
      pick_goal 9
      pick_goal 10
      all_goals try simp [*]
      · change _ = List.filterMap _ (s.add (k .child)).pool
        simp [ConcState.add]
      · exact Hhandle
    · -- Kill case
      iintro Ht %h; rcases Hhandle with ⟨i, t', hi, Hget, HC⟩; imodintro
      let f := λ t (P: (ITree GE GR → PROP)) => iprop(|={⊤, ∅}=> P t)
      iexists t', ConcState.yield s.pool i hi, f t',
        (ConcState.yield s.pool i hi).pool.filterMap (Option.map f), []
      rw [h]
      simp_all only
      simp_all only [List.nil_append, Algebra.BigOpL.bigOpL_nil]
      isplit
      ipureintro
      rotate_left
      isplit
      ipureintro
      pick_goal 2
      isplit
      ipureintro
      pick_goal 2
      isplit
      ipureintro
      pick_goal 2
      iintro %P
      iintro H4_1
      imod Ht with Ht
      icases Ht with %H5_1
      simp_all only
      iexact H4_1
      pick_goal 2
      pick_goal 3
      pick_goal 4
      all_goals try simp [*]
      · simpa [f, ConcState.yield] using filterMap_set_perm f s.pool i (some t') none hi Hget
      · rfl
    · -- Yield case
      iintro >Ht %h; rcases Hhandle with ⟨i, t', hi, Hget, HC⟩
      iapply fupd_mask_intro (by simp); iintro Hemp
      let f := λ t (P : ITree GE GR → PROP) => iprop(|={⊤, ∅}=> P t)
      let tp' := s.pool.set s.curr (some (k ⟨⟩))
      have hi' : i < tp'.length := by simpa [tp'] using hi
      iexists t', ConcState.yield tp' i hi', f t',
        (ConcState.yield tp' i hi').pool.filterMap (Option.map f), [f (k ⟨⟩)]
      rw [h]
      simp_all only [List.cons_append, List.nil_append, Algebra.BigOpL.bigOpL_cons,
        Algebra.BigOpL.bigOpL_nil]
      isplit
      ipureintro
      rotate_left
      isplit
      ipureintro
      pick_goal 2
      isplitl [Ht]
      isplit
      iexact Ht
      ipureintro
      pick_goal 2
      isplit
      ipureintro
      pick_goal 2
      iintro %P
      iintro H4_1
      imod Hemp with Hemp
      icases Hemp with #H5_1
      iexact H4_1
      pick_goal 2
      pick_goal 3
      pick_goal 4
      all_goals try simp [*]
      · apply HC
      · simpa [f, ConcState.yield, tp', h] using
        (filterMap_set_perm f tp' i (some t') none hi' Hget).trans
          (filterMap_set_perm f s.pool s.curr none (some (k ⟨⟩))
            s.curr_in_pool s.curr_is_none)
      · rfl

end exec
