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

/-- Section 2.2.1: an ordinary platform must solve both branches of a disjunction. -/
example (ℓ₁ ℓ₂ : Nat) :
    ((ℓ₁ ↦ 1) ∨ (ℓ₂ ↦ 2)) -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready := by
  ibubble

/-- Section 2.2.2: a linear platform must find a disjoint resource allocation. -/
example (ℓ₁ ℓ₂ : Nat) :
    ((ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2)) -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready ∗ (ℓ₂ ↦ 2) := by
  ibubble

/-- Section 2.3: an ordinary platform is nested inside a linear platform. -/
example (ℓ₁ ℓ₂ ℓ₃ : Nat) :
    (ℓ₁ ↦ 1) ∨ (ℓ₂ ↦ 2) -∗
    ℓ₃ ↦ 3 -∗
    □ (ℓ₁ ↦ 1 -∗ ready) -∗
    □ (ℓ₂ ↦ 2 -∗ ready) -∗
    ready ∗ (ℓ₃ ↦ 3) := by
  ibubble

/-- Section 2.4: two subgoals share an unknown proposition and form a dependent group. -/
example (req : PROP → PROP) (ℓ₁ ℓ₂ ℓ₃ : Nat) :
    □ (∀ P : PROP, req P -∗ P -∗ (ℓ₃ ↦ 3) -∗ ready) -∗
    req iprop((ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2)) -∗
    (ℓ₁ ↦ 1) ∗ (ℓ₂ ↦ 2) ∗ (ℓ₃ ↦ 3) -∗
    ready := by
  ibubble

set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d80
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    (hDecoy0 : P12 ⊢ Q3)
    (hDecoy1 : P14 ⊢ Q6)
    (hDecoy2 : P10 ⊢ Q5)
    (hDecoy3 : P9 ⊢ Q7)
    (hDecoy4 : P11 ⊢ Q6)
    (hDecoy5 : P11 ⊢ Q7)
    (hDecoy6 : P7 ⊢ Q5)
    (hDecoy7 : P13 ⊢ Q0)
    (hDecoy8 : P10 ⊢ Q4)
    (hDecoy9 : P6 ⊢ Q4)
    (hDecoy10 : P11 ⊢ Q3)
    (hDecoy11 : P14 ⊢ Q11)
    (hDecoy12 : P4 ⊢ Q2)
    (hDecoy13 : P12 ⊢ Q9)
    (hDecoy14 : P14 ⊢ Q12)
    (hDecoy15 : P11 ⊢ Q1)
    (hDecoy16 : P10 ⊢ Q7)
    (hDecoy17 : P9 ⊢ Q2)
    (hDecoy18 : P12 ⊢ Q6)
    (hDecoy19 : P11 ⊢ Q8)
    (hDecoy20 : P2 ⊢ Q1)
    (hDecoy21 : P4 ⊢ Q1)
    (hDecoy22 : P7 ⊢ Q4)
    (hDecoy23 : P13 ⊢ Q8)
    (hDecoy24 : P12 ⊢ Q4)
    (hDecoy25 : P14 ⊢ Q2)
    (hDecoy26 : P11 ⊢ Q9)
    (hDecoy27 : P8 ⊢ Q3)
    (hDecoy28 : P14 ⊢ Q13)
    (hDecoy29 : P10 ⊢ Q2)
    (hDecoy30 : P5 ⊢ Q2)
    (hDecoy31 : P6 ⊢ Q1)
    (hDecoy32 : P10 ⊢ Q1)
    (hDecoy33 : P10 ⊢ Q9)
    (hDecoy34 : P14 ⊢ Q4)
    (hDecoy35 : P12 ⊢ Q5)
    (hDecoy36 : P5 ⊢ Q4)
    (hDecoy37 : P7 ⊢ Q1)
    (hDecoy38 : P9 ⊢ Q4)
    (hDecoy39 : P5 ⊢ Q3)
    (hDecoy40 : P8 ⊢ Q5)
    (hDecoy41 : P13 ⊢ Q9)
    (hDecoy42 : P12 ⊢ Q7)
    (hDecoy43 : P12 ⊢ Q2)
    (hDecoy44 : P6 ⊢ Q3)
    (hDecoy45 : P5 ⊢ Q0)
    (hDecoy46 : P6 ⊢ Q0)
    (hDecoy47 : P8 ⊢ Q1)
    (hDecoy48 : P10 ⊢ Q8)
    (hDecoy49 : P7 ⊢ Q6)
    (hDecoy50 : P13 ⊢ Q3)
    (hDecoy51 : P4 ⊢ Q3)
    (hDecoy52 : P12 ⊢ Q10)
    (hDecoy53 : P11 ⊢ Q4)
    (hDecoy54 : P7 ⊢ Q2)
    (hDecoy55 : P11 ⊢ Q10)
    (hDecoy56 : P14 ⊢ Q1)
    (hDecoy57 : P11 ⊢ Q0)
    (hDecoy58 : P13 ⊢ Q10)
    (hDecoy59 : P8 ⊢ Q0)
    (hDecoy60 : P6 ⊢ Q2)
    (hDecoy61 : P13 ⊢ Q4)
    (hDecoy62 : P4 ⊢ Q0)
    (hDecoy63 : P11 ⊢ Q2)
    (hDecoy64 : P8 ⊢ Q4)
    (hDecoy65 : P5 ⊢ Q1)
    (hDecoy66 : P11 ⊢ Q5)
    (hDecoy67 : P7 ⊢ Q3)
    (hDecoy68 : P14 ⊢ Q5)
    (hDecoy69 : P13 ⊢ Q1)
    (hDecoy70 : P3 ⊢ Q1)
    (hDecoy71 : P12 ⊢ Q0)
    (hDecoy72 : P14 ⊢ Q7)
    (hDecoy73 : P10 ⊢ Q3)
    (hDecoy74 : P12 ⊢ Q1)
    (hDecoy75 : P10 ⊢ Q6)
    (hDecoy76 : P14 ⊢ Q3)
    (hDecoy77 : P9 ⊢ Q6)
    (hDecoy78 : P13 ⊢ Q2)
    (hDecoy79 : P9 ⊢ Q0)
    (hDecoy80 : P7 ⊢ Q0)
    (hDecoy81 : P14 ⊢ Q0)
    (hDecoy82 : P8 ⊢ Q6)
    (hDecoy83 : P14 ⊢ Q10)
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100

end BubbleTest.Example
