-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.Basic

public meta section

namespace Bubble.Forward

open Lean Elab Tactic Meta

initialize registerTraceClass `ibubble.forward

-- TODO: Implement forward theorem rules using the shared RuleRunner interface.

end Bubble.Forward
