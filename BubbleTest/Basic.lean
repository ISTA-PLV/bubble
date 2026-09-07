module

public import Iris.BI
public import Iris.ProofMode
public import Bubble

@[expose] public section

namespace Iris.Tests
open Iris.BI

-- Identity test
example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble

/- A `False` hypothesis is closed by the low-probability empty `icases` rule. -/
example [BI PROP] (P : PROP) : False ⊢ P := by
  ibubble

/- Bubble replay also records the selected path for `Try this` generation. -/
example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble

/- Bubble search joins independently solved full-context siblings. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by
  ibubble

/- Nested platforms bubble their selected combinations upward. -/
example [BI PROP] (P Q R : PROP) : P ∗ Q ∗ R ⊢ R ∗ Q ∗ P := by
  ibubble

/- The first local choices may conflict; later alternatives unlock the join. -/
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ (P ∨ Q) ∗ (P ∨ Q) := by
  ibubble

/- Case-split platforms share, rather than partition, their branch context. -/
example [BI PROP] [BIAffine PROP] (P Q R : PROP) :
    (P ∨ Q) ∗ (P -∗ R) ∗ (Q -∗ R) ⊢ R := by
  ibubble

/- Sibling bubbles must agree on the existential witness metavariable.  The
first locally successful P/Q choices may disagree, so search must retain later
compatible alternatives. -/
example [BI PROP] [BIAffine PROP] (P Q : Nat → PROP) :
    P 1 ∗ P 2 ∗ Q 2 ∗ Q 1 ⊢ ∃ x, P x ∗ Q x := by
  ibubble

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble bestFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble depthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble breadthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble depthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble breadthFirst

example [BI PROP] (P : PROP) : P ⊢ P := by
  ibubble maxDepth 200

example [BI PROP] (P : PROP) : P ⊢ P := by
  -- ibubble
  ibubble

/- Normalization rewrites both the spatial context and target using Lean equalities. -/
example [BI PROP] (P Q : Nat → PROP) (n m : Nat) (h : n = m) :
    P n ∗ Q n ⊢ Q m ∗ P m := by
  ibubble

-- Basic context split test
example [BI PROP] (P Q R : PROP) : P ∗ Q ∗ R ⊢ R ∗ Q ∗ P:= by
  ibubble

-- Multiple context split test
example [BI PROP] [BIAffine PROP] (P Q R S T: PROP) :
    T -∗ P -∗ Q -∗ R -∗ S -∗ P ∗ Q ∗ R ∗ S := by
  ibubble

example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
    P -∗ Q  -∗ (P -∗ Q -∗ R) -∗ (P -∗ R)  -∗ (Q -∗ P -∗ S) -∗ (Q -∗ S) -∗ (R ∗ S) := by
  iintro HP HQ H1 H2 H3 H4
  ibubble

/- Nested context split test -/
example [BI PROP] (P Q R S : PROP) :
    P -∗ Q -∗ R -∗ ((P ∗ Q) -∗ R -∗ S) -∗ S := by
  ibubble

example [BI PROP] (P Q R S : PROP) :
    Q -∗ R -∗ (P -∗ Q -∗ S) -∗ (R ∗ (P -∗ S)) := by
  ibubble

example [BI PROP] (P Q R : PROP) :
    P ∗ (∀ x, P -∗ ⌜x = 0⌝ -∗ (Q ∗ (True -∗ R))) ⊢ R ∗ Q := by
  ibubble pureBy trivial

/-- Tests `iapply` with two wands and subgoals -/
@[ibubble forward 100% backward 100%]
example [BI PROP] (P Q : Nat → PROP) :
    (P 1 -∗ P 2 -∗ Q 1) ⊢ □ P 1 -∗ P 2 -∗ Q 1 := by
  ibubble

/-- Tests `ispecialize` with named subgoal -/
@[ibubble backward 100%]
example [BI PROP] (Q : PROP) (φ : Prop) (hφ : φ):
    P ⊢ (⌜φ⌝ -∗ P -∗ ⌜True⌝ -∗ Q) -∗ Q := by
  ibubble pureBy grind

/-- Tests `ispecialize` with mixed forall and wand specialization -/
-- A very useful example: we can identify the iprop in the target proposition
@[ibubble forward 100%]
example [BI PROP] (Q : Nat → PROP) :
    ⊢ □ P1 -∗ P2 -∗ (□ P1 -∗ (∀ x, P2 -∗ Q x)) -∗ Q y := by
  ibubble

/- Tests `applyHyps` can parse Lean hypothesis to apply -/
example [BI PROP] (P Q : Nat → PROP) (H : ∀ x, ⊢ P x -∗ Q x) :
    P 1 -∗ Q 1 := by
  ibubble

/-- Tests `iapply` with forall specialization -/
example [BI PROP] (P Q : α → PROP) (a b : α) :
    P a ∗ (∀ x, ∀ y, P x -∗ Q y) ⊢ Q b := by
  ibubble

/-- One more example for ibubble, context refill -/
example [BI PROP] (P Q R : α → PROP) (a b c : α)
    (H : ⊢ ∀ x, ∀ y, ∀ z, P x -∗ Q y -∗ R z) : P a ∗ Q b ⊢ R c := by
  ibubble

/-- Tests `iexact` with fupd -/
example [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP]
    (E : CoPset) (P : PROP) : P ⊢ |={E}=> P := by
  ibubble

/-- Tests `iapply` with intuitionistic forall from Lean -/
example [BI PROP] (P Q : α → PROP) (a b : α) (H : ⊢ □ ∀ x, ∀ y, P x -∗ Q y) : P a ⊢ Q b := by
  ibubble

example [BI PROP] [BIUpdate PROP] (P : PROP) : |==> |==> P ⊢ |==> P := by
  ibubble

example [BI PROP] [BIAffine PROP] (P Q R S : PROP) :
    S -∗ (P ∨ Q) -∗ (P -∗ R) -∗ (Q -∗ S -∗ R) -∗ (Q -∗ R) -∗ (R ∗ S) := by
  ibubble

example [BI PROP] (P Q : α → PROP) (R : PROP) :
    P a -∗ □ (∀ x, (P x -∗ Q x) ∧ R) -∗ Q a := by
  ibubble

example [BI PROP] (P : α → PROP) (Q : β → PROP) (R : α → β → PROP) (S : PROP):
    □ (∀ x y, P x -∗ Q y -∗ R x y -∗ S) -∗
    P a -∗ Q b -∗
    R a b -∗ S := by
  ibubble

/-- Tests `iexists` with anonymous metavariable -/
example [BI PROP] : ⊢@{PROP} ∃ x, ⌜x = 42⌝ := by
  ibubble pureBy grind

example [BI PROP] (P : α → PROP) : P a ⊢ ∃ x, P x := by
  ibubble

section LocalRuleFrontend

/- A backward equivalence is indexed in both directions, and its ordinary
Lean proposition parameter is exposed as a pure Iris premise. -/
structure BackwardEquivWitness [BI PROP] (P : PROP) : Prop where
  equiv : iprop(P ∧ True) ⊣⊢ P

theorem backward_bientails_with_pure [BI PROP] {P : PROP}
    (h : BackwardEquivWitness P) : iprop(P ∧ True) ⊣⊢ P := h.equiv

example [BI PROP] (P : PROP) : iprop(P ∧ True) ⊢ P := by
  ibubble with [backward backward_bientails_with_pure]

example [BI PROP] (P : PROP) (h : BackwardEquivWitness P) : P ⊢ iprop(P ∧ True) := by
  set_option trace.ibubble.ruleIndex true in
  set_option trace.ibubble.backward true in
  ibubble pureBy assumption with [backward backward_bientails_with_pure]

theorem local_rule_added_test [BI PROP] : ⊢@{PROP} ⌜True ∧ True⌝ := by
  ipureintro
  exact And.intro True.intro True.intro

example [BI PROP] : ⊢@{PROP} ⌜True ∧ True⌝ := by
  ibubble noSimp with [backward local_rule_added_test 75%]

theorem removable_rule_test [BI PROP] : ⊢@{PROP} ⌜True ∧ True⌝ := by
  ipureintro
  exact And.intro True.intro True.intro

attribute [local ibubble backward 100%] removable_rule_test

/--
error: unsolved goals
-/
#guard_msgs (substring := true) in
example [BI PROP] : ⊢@{PROP} ⌜True ∧ True⌝ := by
  ibubble noSimp without [backward removable_rule_test]

example [BI PROP] : ⊢@{PROP} ⌜True ∧ True⌝ := by
  ibubble noSimp

end LocalRuleFrontend
