-- SPDX-License-Identifier: Apache-2.0
module

public meta import Iris.ProofMode.SynthInstance

public meta section

namespace Iris.ProofMode.Aesop

open Lean Meta Qq Std

/- Treat typeclass-search exceptions as failed speculative probes and restore the metavariable state. -/
def trySynthInstanceProbeQ {u : Level} (α : Q(Sort u)) :
    MetaM (LOption (Q($α) × Std.HashSet MVarId)) := do
  let preState ← saveState
  try
    ProofMode.trySynthInstance α
  catch _ =>
    preState.restore
    return .none

end Iris.ProofMode.Aesop
