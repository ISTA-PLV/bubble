-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Core.Types

public meta section

namespace Bubble

/-- What closes the forward path stored by a bubble. -/
inductive BubbleEnd where
  /- Normalization closes a goal directly. -/
  | normalization
  /- A rule application closes without generating subgoals. -/
  | ruleApplication
  /- A child platform completes and emits a joined candidate. -/
  | platformEmission (children : Array BubbleId)
  deriving Inhabited, BEq

/--
  A proof result while it is rising through unary platforms.
  It is not given an ID or entered in the global store until it reaches a
  coordination boundary.
-/
structure RisingBubble where
  endKind  : BubbleEnd
  /- Selected Rapps from the next boundary down to the closing step. -/
  forward  : Array RappId := #[]
  consumed : Array IrisHyp := #[]
  metaInfo : Array MetaAssignment := #[]

-- The central certificate type intentionally shares the project's namespace name.
set_option linter.iris.dupNamespace false in
/-- A rising bubble materialized at an unrestricted/linear platform or at the root. -/
structure Bubble where
  id       : BubbleId
  goal     : GoalId
  consumed : Array IrisHyp
  metaInfo : Array MetaAssignment
  /- A residual goal may only be reconstructed after this bubble. -/
  pre?     : Option BubbleId := none
  /- What closes the selected forward path. -/
  endKind  : BubbleEnd
  /- Selected Rapps from this boundary down to the closing step. -/
  forward  : Array RappId := #[]

end Bubble
