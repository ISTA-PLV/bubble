module

public meta import Bubble.Rule.Backward
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

namespace Bubble.RuleBuilder

def run : RuleBuilder → RuleRunner
  | .tactic .identity => Rule.Tactic.Identity.run
  | .tactic .applyHyps => Rule.Tactic.ApplyHyps.run
  | .tactic .haveHyps => Rule.Tactic.HaveHyps.run
  | .tactic .icases => Rule.Tactic.ICases.run
  | .tactic .icasesFalse => Rule.Tactic.ICases.runFalse
  | .tactic .ipureIntro => Rule.Tactic.IPureIntro.run
  | .tactic .ileft => Rule.Tactic.ILeftRight.runLeft
  | .tactic .iright => Rule.Tactic.ILeftRight.runRight
  | .tactic .iexist => Rule.Tactic.IExist.run
  | .tactic .imodIntro => Rule.Tactic.IModIntro.run
  | .tactic .imod => Rule.Tactic.IMod.run
  | .tactic .isplit => Rule.Tactic.ISplit.run
  | .backward _ => Rule.Backward.run
  | .forward => fun _ => return RuleOutput.ofSpecs #[]

end Bubble.RuleBuilder
