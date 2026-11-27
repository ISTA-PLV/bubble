-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Backward
public meta import Bubble.Rule.Forward
public meta import Bubble.Rule.Tactic.Main

public meta section

namespace Bubble.RuleBuilder

/-- Select the runner for a backward, tactic, or forward rule. -/
def run : RuleBuilder → RuleRunner
  | .tactic descr => Bubble.Tactic.run descr
  | .backward _ => Bubble.Backward.run
  | .forward _ => Bubble.Forward.run

end Bubble.RuleBuilder
