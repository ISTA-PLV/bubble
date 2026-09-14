module

import Bubble

public import BubbleTest.IrisITreeScript.Effects.State
public import BubbleTest.IrisITreeScript.Effects.Demonic
public import BubbleTest.IrisITreeScript.Effects.Fail
public import ITree.Effects.Heap
public import Iris.BI.BigOp.BigSepList
public import Iris.Instances.Lib.GhostMap
public import Iris.Instances.Lib.Invariants
public import Iris.Std.HeapInstances

@[expose] public section

-- A heap, represented as a [gmap] of [option val]s, with [None] representing deallocated locations.

namespace IrisITreeScript.Effects

open Iris BI ITree Effects Core

class heapHGpreS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_ghost_varG : GhostMapG GF Loc (Option Val) (Std.ExtTreeMap Loc · compare)

attribute [reducible, instance] heapHGpreS.heapH_ghost_varG

class heapHGS (GF : BundledGFunctors) (Loc Val : Type)
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] where
  heapH_inG : heapHGpreS GF Loc Val
  heapH_heap_name : GName
  heapH_inv_name_postfix : String

attribute [reducible, instance] heapHGS.heapH_inG

def heapH_inv_name {GF : BundledGFunctors} {Loc Val : Type}
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
    [G : heapHGS GF Loc Val] : Namespace :=
  (nroot.@"heapH").@G.heapH_inv_name_postfix

def pointsto {GF : BundledGFunctors} {Loc Val : Type}
    [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
    [G : heapHGS GF Loc Val] (l : Loc) (v : Option Val) (dq : DFrac) : IProp GF :=
  ghost_map_elem (G.heapH_heap_name) dq l v

notation:50 l:50 " ↦? " v:50 => pointsto l v (DFrac.own 1)
notation:50 l:50 " ↦{" dq "}? " v:50 => pointsto l v dq
notation:50 l:50 " ↦ " v:50 => pointsto l (some v) (DFrac.own 1)
notation:50 l:50 " ↦{" dq "} " v:50 => pointsto l (some v) dq

section handler

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] [DecidableEq Loc]
variable [G : heapHGS GF Loc Val]

-- Half of the authoritative view of the current heap into an invariant
-- so that we can know that someone else won't change it while we have control
def heap_inv : IProp GF :=
  inv (heapH_inv_name (G := G)) iprop(
    ∃ σ, ghost_map_auth (K := Loc) (V := Option Val)
      G.heapH_heap_name (DFrac.own $ Qp.half 1) σ
  )

instance heap_inv_persistent : Persistent (heap_inv (G := G)) := by
  unfold heap_inv
  infer_instance

def stateInterp_heap (σ : heapE.T Loc Val) : IProp GF := iprop(
  ghost_map_auth (K := Loc) (V := Option Val)
    G.heapH_heap_name (DFrac.own $ Qp.half 1) σ
  ∧ heap_inv (G := G)
)

def heapH : IHandler (IProp GF) (heapE Loc Val) :=
  stateH stateInterp_heap

end handler

section initialization

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc] [DecidableEq Loc]
variable [Gpre : heapHGpreS GF Loc Val]

attribute [local simp] heap_inv heapH_inv_name stateInterp_heap pointsto

theorem heapH_init  (σ : heapE.T Loc Val) :
    ⊢ |={∅}=> ∃ G : heapHGS GF Loc Val,
      heap_inv (G := G) ∗
      stateInterp_heap σ ∗
      bigSepM (M := (Std.ExtTreeMap Loc · compare)) (λ k v => k ↦? v) σ := by
  icases (ghost_map_alloc (K := Loc) (V := Option Val) σ) with Hgmap
  imod Hgmap; icases Hgmap with ⟨%γ, ⟨⟨Hauth, Hauth'⟩, Hfrag⟩⟩
  imod (inv_alloc ((nroot.@"heapH").@"") ∅
    (∃ σ, ghost_map_auth (K := Loc) (V := Option Val) γ (.own $ .half 1) σ)) $$ [Hauth] with #Hinv
  · iexists _
    iexact Hauth
  · imodintro; iexists ⟨Gpre, γ, ""⟩
    simp_all only [heap_inv, heapH_inv_name, stateInterp_heap, pointsto]
    isplit
    iexact Hinv
    isplitl [Hauth']
    isplit
    iexact Hauth'
    iexact Hinv
    iexact Hfrag

end initialization

section wpi_rules

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
variable {Loc Val : Type} [Ord Loc] [Std.TransOrd Loc] [Std.LawfulEqOrd Loc]
variable [G : heapHGS GF Loc Val]
variable {E : Effect} {H : IHandler (IProp GF) E}
variable [heapE Loc Val -< E] [InH (heapH (G := G)) H]

attribute [local simp] Option.join_some

-- Note: we can extend the following theorems to `Ms,Me` version by having `|={Ms,Me}=> Φ v`
@[ibubble 75%]
theorem wpi_storeOpt M (l : Loc) (v v' : Option Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦? v' -∗ Φ v) -∗
    WPi (storeOpt l v') @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto storeOpt
  iapply wpi_bind' (M \ ↑(heapH_inv_name (G := G))); iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨HauthState, #Hinv⟩
  imod inv_acc_timeless Hmask $$ Hinv with ⟨⟨%σinv, HauthInv⟩, Hclose⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv HauthState; subst σinv
  imodintro; isplitl [HauthState]
  · isplit
    iexact HauthState
    iexact Hinv

  -- look up and insert operations
  ihave %Hlookup := ghost_map_lookup $$ HauthInv Hpt
  have Hlookup : σ[l]? = some v := by
    simpa [Iris.Std.get?] using Hlookup
  have Hinsert : σ.insert l v' = Std.insert (M := (Std.ExtTreeMap Loc · compare)) σ l v'  := by
    apply Std.ExtTreeMap.ext_getElem?; intro k
    simp only [Iris.Std.insert, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]
  rw [Hlookup, Hinsert]
  simp only [Option.join_some]

  iapply wpi_bind' M; iapply wpi_set
  unfold stateInterp_heap heap_inv
  iintro %σ' ⟨HauthState, -⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv HauthState; subst σ'
  icombine HauthInv HauthState as Hauth
  imod ghost_map_update v' $$ Hauth Hpt with ⟨⟨Hauth, Hauth'⟩, Hpt⟩
  imod Hclose $$ [Hauth'] with -
  · iexists Std.insert (M := (Std.ExtTreeMap Loc · compare)) σ l v'
    iexact Hauth'
  isplitl [Hauth]
  isplitl [Hauth]
  iexact Hauth
  iexact Hinv
  iapply IrisITreeScript.Core.wpi_pure
  iapply Hwand
  iexact Hpt

@[ibubble 75%]
theorem wpi_store? M (l : Loc) (v : Option Val) (v' : Val) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦? v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store? l v') @> H; M {{ Φ }} := by
  unfold store?
  iintro %x
  iintro H0_1
  iintro H0_2
  iapply IrisITreeScript.Effects.wpi_storeOpt $$ [ H0_1 ]
  assumption
  pick_goal 2
  iintro H1_1
  iapply H0_2
  iexact H1_1
  iexact H0_1

@[ibubble 75%]
theorem wpi_load? M (l : Loc) (v : Val) (dq : DFrac) (Φ : Option Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ (some v)) -∗
    WPi (load? l) @> H; M {{ Φ }} := by
  iintro %Hmask Hpt Hwand; unfold pointsto load?
  iapply wpi_bind; iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩
  ihave %Hlookup := ghost_map_lookup $$ Hauth Hpt
  have Hlookup : σ[l]? = some (some v) := by
    simpa [Iris.Std.get?] using Hlookup
  rw [Hlookup]
  simp_all only [Option.join_some]
  isplitl [Hauth]
  isplitl [Hauth]
  iexact Hauth
  iexact Hinv
  iapply IrisITreeScript.Core.wpi_pure
  iapply Hwand
  iexact Hpt

section fail

variable [failE -< E]

@[ibubble 75%]
theorem wpi_store! M (l : Loc) (v v' : Val) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦ v -∗
    (l ↦ v' -∗ Φ v) -∗
    WPi (store! l v') @> H; M {{ Φ }} := by
  unfold store!
  iintro %x
  iintro H0_1
  iintro H0_2
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_store? $$ [ H0_1 ]
  assumption
  iexact H0_1
  iintro H2_1
  simp_all only
  iapply IrisITreeScript.Core.wpi_pure
  iapply H0_2
  iexact H2_1

@[ibubble 75%]
theorem wpi_load! M (l : Loc) (v : Val) (dq : DFrac) (Φ : Val → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    l ↦{dq} v -∗
    (l ↦{dq} v -∗ Φ v) -∗
    WPi (load! l) @> H; M {{ Φ }} := by
  unfold load!
  iintro %x
  iintro H0_1
  iintro H0_2
  iapply IrisITreeScript.Core.wpi_bind
  iapply IrisITreeScript.Effects.wpi_load? $$ [ H0_1 ]
  assumption
  iexact H0_1
  iintro H2_1
  simp_all only
  iapply IrisITreeScript.Core.wpi_pure
  iapply H0_2
  iexact H2_1

end fail

class LawfulLoc (Loc : Type) [Ord Loc] extends Zero Loc, HAdd Loc Int Loc where
  decEq : DecidableEq Loc
  add_zero (l : Loc) : l + (0 : Int) = l
  add_nat_inj (l : Loc) : Function.Injective (λ i => l + Int.ofNat i)
  add_pos_nle (l : Loc) (m : Nat) :
    ¬(compare (l + (1 : Int) + (m : Int)) l).isLE = true

attribute [reducible, instance] LawfulLoc.decEq
attribute [simp] LawfulLoc.add_zero

theorem extTreeMap_insertMany_eq_ofList_union {K : Type _} {V : Type _}
    [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] [DecidableEq K]
    (m : Std.ExtTreeMap K V compare) (entries : List (K × V))
    (Hnodup : Iris.Std.NoDupKeys entries) :
    m.insertMany entries = Std.PartialMap.union (M := (Std.ExtTreeMap K · compare))
      (Std.PartialMap.ofList (M := (Std.ExtTreeMap K · compare)) entries) m := by
  apply Std.ExtTreeMap.ext_getElem?; intro k
  simp [Iris.Std.PartialMap.union, Iris.Std.merge]
  by_cases Hmem : ∃ w, (k, w) ∈ entries
  · rcases Hmem with ⟨w, Hw⟩
    rw [Std.ExtTreeMap.getElem?_insertMany_list_of_mem ?_
      ((List.pairwise_map.mp
          (List.nodup_iff_pairwise_ne.mp Hnodup)).imp fun Hne Heq =>
            Hne (Std.LawfulEqOrd.compare_eq_iff_eq.mp Heq)) Hw]
    change some w = Option.merge _ (Iris.Std.get? (M := (Std.ExtTreeMap K · compare)) _ k) _
    simp only [Iris.Std.LawfulPartialMap.get?_ofList_some Hw Hnodup]
    cases m[k]? <;> rfl
    simp
  · rw [Std.ExtTreeMap.getElem?_insertMany_list_of_contains_eq_false ?_]
    change m[k]? = Option.merge _
      (Iris.Std.get? (M := (Std.ExtTreeMap K · compare)) _ k) _
    simp only [Iris.Std.LawfulPartialMap.get?_ofList_none Hmem Hnodup]
    cases m[k]? <;> rfl
    rw [← Bool.not_eq_true]
    intro Hcontains
    rcases List.mem_map.mp (List.contains_iff_mem.mp Hcontains) with
      ⟨⟨k', w⟩, Hw, Hk⟩
    apply Hmem; exact ⟨w, Hk ▸ Hw⟩

section alloc

variable [demonicE Loc -< E] [InH (demonicH (PROP := IProp GF) Loc) H]
variable [LawfulLoc Loc]

attribute [local simp] pointsto

@[ibubble 75%]
theorem wpi_allocN M (n : Nat) (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    (∀ l : Loc, ([∗list] i ∈ .range n, (l + Int.ofNat i) ↦ v) -∗ Φ l) -∗
    WPi (allocN n v LawfulLoc.add_pos_nle) @> H; M {{ Φ }} := by
  iintro %Hmask Hwand; unfold allocN
  iapply wpi_bind' (M \ ↑(heapH_inv_name (G := G))); iapply wpi_get
  unfold stateInterp_heap heap_inv
  iintro %σ ⟨Hauth, #Hinv⟩
  imod inv_acc_timeless Hmask $$ Hinv with ⟨⟨%σinv, HauthInv⟩, Hclose⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv Hauth; subst σinv
  imodintro; isplitl [Hauth]
  · isplit
    iexact Hauth
    iexact Hinv
  iapply wpi_bind; iapply wpi_demonic (Hi := inhabited_free_locs σ LawfulLoc.add_pos_nle)
  iintro %r; rcases r with ⟨l, Hfree⟩; simp only
  iapply wpi_bind' M; iapply wpi_set
  unfold stateInterp_heap heap_inv
  iintro %σ' ⟨Hauth', -⟩
  ihave %Heq := ghost_map_auth_agree $$ HauthInv Hauth'; subst σ'
  icombine HauthInv Hauth' as Hauth;

  -- We do not need to care about the orders
  let entries := (List.range n).map λ m => (l + Int.ofNat m, some v)
  let σnew := Std.PartialMap.ofList (M := (Std.ExtTreeMap Loc · compare)) entries
  let σsum := Std.PartialMap.union (M := (Std.ExtTreeMap Loc · compare)) σnew σ

  -- New added entries do not have duplicated elements and the unioned hold the same elements
  have Hnodup : Std.NoDupKeys entries := by
    unfold Iris.Std.NoDupKeys entries
    simp [List.map_map]
    exact List.nodup_map_of_injective
      (LawfulLoc.add_nat_inj l) List.nodup_range
  have HinsertMany : σ.insertMany entries = σsum := by
    simpa only [σnew] using extTreeMap_insertMany_eq_ofList_union σ entries Hnodup
  have HinsertMany' :
      σ.insertMany ((List.range n).map fun (i : Nat) => (l + (i : Int), some v)) = σsum := by
    simpa [entries, σsum] using HinsertMany
  have HbigSepMap := equiv_iff.mp (BigSepL.bigSepL_map
    (l := List.range n)
    (Φ := λ (_ : Nat) (kv : Loc × Option Val) =>
      ghost_map_elem (GF := GF) G.heapH_heap_name (DFrac.own 1) kv.1 kv.2)
    (l + Int.ofNat ·, some v))

  imod ghost_map_insert_big σnew $$ Hauth with ⟨Hauth, Hpts⟩
  · -- Prove σnew ##ₘ σ
    unfold Std.PartialMap.disjoint; intro k Hk
    rcases Option.isSome_iff_exists.mp Hk.1 with ⟨w, Hw⟩
    have Hmem := Iris.Std.LawfulFiniteMap.mem_of_mem_ofList Hw
    simp only [entries, List.mem_map] at Hmem
    rcases Hmem with ⟨i, Hi, Hki⟩
    have Hkey : l + Int.ofNat i = k := congrArg Prod.fst Hki
    rw [← Hkey] at Hk
    apply Hfree i $ List.mem_range.mp Hi
    simpa [Iris.Std.get?] using Hk.2
  icases Hauth with ⟨HauthInv, HauthState⟩
  imod Hclose $$ [HauthInv] with -
  · simp_all only
    simp_all only [Int.ofNat_eq_natCast]
    iexists _
    iexact HauthInv
  · rw [HinsertMany']
    simp_all only
    simp_all only [Int.ofNat_eq_natCast, pointsto]
    isplitl [HauthState]
    isplitl [HauthState]
    iexact HauthState
    iexact Hinv
    iapply IrisITreeScript.Core.wpi_pure
    iapply Hwand
    iapply HbigSepMap
    imodintro
    iapply Iris.BI.BigSepM.bigSepM_ofList
    assumption
    iexact Hpts

@[ibubble 75%]
theorem wpi_alloc M (v : Val) (Φ : Loc → IProp GF) :
    ↑(heapH_inv_name (G := G)) ⊆ M →
    (∀ l, l ↦ v -∗ Φ l) -∗
    WPi (alloc v LawfulLoc.add_pos_nle) @> H; M {{ Φ }} := by
  unfold alloc
  iintro %x
  iintro H0_1
  simp_all only [pointsto]
  iapply IrisITreeScript.Effects.wpi_allocN
  assumption
  iintro %l
  iintro H1_1
  simp_all only [pointsto, Int.ofNat_eq_natCast, List.range_one, Algebra.BigOpL.bigOpL_cons,
    Int.cast_ofNat_Int, LawfulLoc.add_zero, Algebra.BigOpL.bigOpL_nil]
  icases H1_1 with ⟨H1_2, H1_3⟩
  icases H1_3 with #H1_4
  iapply H0_1
  iexact H1_2

end alloc

end wpi_rules

end IrisITreeScript.Effects
