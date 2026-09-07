module

public import Iris.BI
public import Iris.ProofMode
public import Bubble

@[expose] public section

namespace BubbleTest.Example

open Iris Iris.BI

variable {PROP : Type} [Iris.BI PROP]
variable (pointsTo : Nat → Nat → PROP) (ready : PROP)

local infix:55 " ↦ " => pointsTo

/-- Section 2.1: proof search must recover from the stuck `ℓ₁ ↦ 1` branch. -/
example (ℓ₁ ℓ₂ : Nat) :
    ℓ₂ ↦ 2 -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready := by
  ibubble

/-- Section 2.2: an ordinary platform must solve both branches of a disjunction. -/
example (ℓ₁ ℓ₂ : Nat) :
    ((ℓ₁ ↦ 1) ∨ (ℓ₂ ↦ 2)) -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready := by
  ibubble

/-- Section 2.3: a linear platform must find a disjoint resource allocation. -/
example (ℓ₁ ℓ₂ : Nat) :
    ((ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2)) -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready ∗ (ℓ₂ ↦ 2) := by
  ibubble

/-- Section 2.4: an ordinary platform is nested inside a linear platform. -/
example (ℓ₁ ℓ₂ ℓ₃ : Nat) :
    (ℓ₁ ↦ 1) ∨ (ℓ₂ ↦ 2) -∗
    ℓ₃ ↦ 3 -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready ∗ (ℓ₃ ↦ 3) := by
  ibubble

/-- Section 6: two subgoals share an unknown proposition and form a dependent group. -/
example (req : PROP → PROP) (ℓ₁ ℓ₂ ℓ₃ : Nat) :
    □ (∀ P : PROP, req P -∗ P -∗ (ℓ₃ ↦ 3) -∗ ready) -∗
    req iprop((ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2)) -∗
    (ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2) ∗ (ℓ₃ ↦ 3) -∗
    ready := by
  ibubble

end BubbleTest.Example
