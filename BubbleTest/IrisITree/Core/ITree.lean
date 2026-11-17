-- SPDX-License-Identifier: Apache-2.0
module

public import Iris.Algebra.OFE
public import ITree.Definition

@[expose] public section

namespace IrisITree
open ITree Iris

instance {E R} : COFE (ITree E R) := COFE.ofDiscrete _
instance {E R} : OFE.Discrete (ITree E R) := ⟨fun h => h⟩

end IrisITree

namespace ITree

open ITree

variable {E R} (t : ITree E R)

@[simp]
theorem interp_trigger_id (t : ITree E R) :
    ITree.interp (λ i => E.trigger i) t = t :=
  ITree.interp_trigger_identity t

section interp_inverse

theorem interp_ret_inv {E1 E2 R} [E1 -< E2] {t : ITree E1 R} {r : R} :
    ITree.interp (λ i => (E1.trigger i : ITree E2 (E1.O i))) t = ret r →
    t = ret r := by
  intro h
  cases t <;> simp only [Effect.trigger] at h ⊢
    <;> have h' := congrArg ITree.unfold h
    <;> simp at h'
  subst h'; rfl

end interp_inverse

end ITree
