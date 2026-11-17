-- SPDX-License-Identifier: Apache-2.0
module

public meta import Bubble.Rule.Tactic.ApplyHyps
public meta import Bubble.Rule.Tactic.HaveHyps
public meta import Bubble.Rule.Tactic.ICases
public meta import Bubble.Rule.Tactic.IExist
public meta import Bubble.Rule.Tactic.ILeftRight
public meta import Bubble.Rule.Tactic.IMod
public meta import Bubble.Rule.Tactic.IModIntro
public meta import Bubble.Rule.Tactic.IPureIntro
public meta import Bubble.Rule.Tactic.ISplit
public meta import Bubble.Rule.Tactic.Identity

public meta section

namespace Bubble.Tactic

/-- Select the runner for a built-in tactic rule. -/
def run : TacticDescr → RuleRunner
  | .identity => Identity.run
  | .applyHyps => ApplyHyps.run
  | .haveHyps => HaveHyps.run
  | .icases => ICases.run
  | .icasesFalse => ICases.runFalse
  | .ipureIntro => IPureIntro.run
  | .ileft => ILeftRight.runLeft
  | .iright => ILeftRight.runRight
  | .iexist => IExist.run
  | .imodIntro => IModIntro.run
  | .imod => IMod.run
  | .isplit => ISplit.run

end Bubble.Tactic
