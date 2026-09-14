module

import Bubble

import Iris.ProofMode
public import BubbleTest.IrisITreeBubble.Core.Wpi
public import ITree.Effects.Conc

@[expose] public section

namespace IrisITreeBubble.Effects

open Iris Iris.BI ITree ITree.Effects IrisITreeBubble.Core

section handler

variable {PROP : Type _} [BI PROP] [BIFUpdate PROP]

def concH : IHandler PROP concE where
  ihandle
    | .fork, Φ, Φs => iprop(Φ .parent ∗ |={⊤, ∅}=> Φs .child)
    | .yield, Φ, _ => iprop(|={∅, ⊤}=> |={⊤, ∅}=> Φ ⟨⟩)
    | .kill, _, _ => iprop(|={∅, ⊤}=> True)
  ihandle_mono := by
    iintro %i %Φ %Φ' %Φs %Φs' HΦwand #Hswand HH
    cases i <;> ibubble

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
  ibubble pureBy simp

@[ibubble 75%]
theorem wpi_fork M (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi t @> H; ⊤ {{ _v, iprop(True) }} -∗
    WPi fork t @> H; M {{Φ}} := by
  unfold fork
  iintro HΦ Ht; iapply wpi_trigger_bind; simp [concH]
  iapply fupd_mask_intro (by simp); iintro Hm
  isplitr [Ht] <;> ibubble pureBy simp with [wpi_wand 1%]

@[ibubble 75%]
theorem wpi_yield (Φ : PUnit → PROP) :
    Φ ⟨⟩ -∗
    WPi yield @> H; ⊤ {{Φ}} := by
  unfold yield
  ibubble pureBy simp

end wpi_rules

section exec

open ITree.Exec IrisITreeBubble.Core

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
      iintro ⟨_, _⟩ %h !>
      iexists _, _, λ P => P (k .parent),
        Ms ++ [(λ P => iprop(|={⊤, ∅}=> P (k .child)))],
        [λ P => P (k .parent), λ P => iprop(|={⊤, ∅}=> P (k .child))]
      ibubble pureStop <;> try simp [*]
      · change _ = List.filterMap _ (s.add (k .child)).pool
        simp [ConcState.add]
      · exact Hhandle
    · -- Kill case
      iintro Ht %h; rcases Hhandle with ⟨i, t', hi, Hget, HC⟩; imodintro
      let f := λ t (P: (ITree GE GR → PROP)) => iprop(|={⊤, ∅}=> P t)
      iexists t', ConcState.yield s.pool i hi, f t',
        (ConcState.yield s.pool i hi).pool.filterMap (Option.map f), []
      ibubble pureStop <;> try simp [*]
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
      ibubble pureStop <;> try simp [*]
      · apply HC
      · simpa [f, ConcState.yield, tp', h] using
        (filterMap_set_perm f tp' i (some t') none hi' Hget).trans
          (filterMap_set_perm f s.pool s.curr none (some (k ⟨⟩))
            s.curr_in_pool s.curr_is_none)
      · rfl

end exec
