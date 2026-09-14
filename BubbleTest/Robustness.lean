module
public meta import BubbleTest.Robustness.Tactics

@[expose] public section
namespace BubbleTest.Robustness
open Iris Iris.BI
set_option linter.unusedVariables false

-- Restored Aesop + eager partition enumeration, through actual ProofMode steps.
example [BI PROP] (P : PROP) : P ⊢ P := by inaive
example [BI PROP] (P Q : PROP) : P ∗ Q ⊢ Q ∗ P := by inaive
example [BI PROP] (P0 P1 Q0 Q1 : PROP)
    (decoy : P1 ⊢ Q0) (canonical0 : P0 ⊢ Q0) (canonical1 : P1 ⊢ Q1) :
    P1 ∗ P0 ⊢ Q0 ∗ Q1 := by inaive
example [BI PROP] (P Q : PROP) (h : P ⊢ Q) : P ∗ P ⊢ Q ∗ Q := by inaive
example [BI PROP] (P Q R : PROP) : P ∗ Q ∗ R ⊢ (R ∗ P) ∗ Q := by inaive
example [BI PROP] (P : PROP) (h : P ⊢ P ∗ P) : P ⊢ P ∗ P := by
  fail_if_success (clear h; inaive)
  exact h
example [BI PROP] (P Q : PROP) (h : P ∗ Q ⊢ P) : P ∗ Q ⊢ P := by
  fail_if_success (clear h; inaive)
  exact h
end BubbleTest.Robustness
