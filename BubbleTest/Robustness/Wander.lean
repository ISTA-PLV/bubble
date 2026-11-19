-- SPDX-License-Identifier: Apache-2.0
module

import Bubble
-- Import the core rules; upstream Wander's HeapLang rules do not build with Iris 4.35.
import Wander.Tactic
import Wander.Rules.Basic

open Iris BI

set_option maxHeartbeats 2000000

namespace BubbleTest.Robustness.Wander

/-- Wander solves the canonical allocation when no rule competes for P1. -/
example [BI PROP] [BIAffine PROP] [FUpd PROP] [BUpd PROP]
    (P0 P1 Q0 Q1 : PROP) :
    □ (P0 -∗ Q0) -∗ □ (P1 -∗ Q1) -∗ P1 ∗ P0 -∗ Q0 ∗ Q1 := by
  wander => finish

/-- The first contention test, with its rules supplied as Lean hypotheses. -/
example [BI PROP] [BIAffine PROP] [FUpd PROP] [BUpd PROP]
    (P0 P1 Q0 Q1 : PROP)
    (_decoy : P1 ⊢ Q0) (canonical0 : P0 ⊢ Q0) (canonical1 : P1 ⊢ Q1) :
    P1 ∗ P0 ⊢ Q0 ∗ Q1 := by
  fail_if_success (solve | wander => finish)
  ibubble noSimp

/-- The contention persists when the same rules are supplied as persistent wands. -/
example [BI PROP] [BIAffine PROP] [FUpd PROP] [BUpd PROP]
    (P0 P1 Q0 Q1 : PROP) :
    □ (P1 -∗ Q0) -∗ □ (P0 -∗ Q0) -∗ □ (P1 -∗ Q1) -∗
    P1 ∗ P0 -∗ Q0 ∗ Q1 := by
  fail_if_success (solve | wander => finish)
  ibubble noSimp

end BubbleTest.Robustness.Wander
