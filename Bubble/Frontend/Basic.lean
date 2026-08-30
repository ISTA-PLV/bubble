module

public section

namespace Bubble

/- Specify strategy. -/
declare_syntax_cat ibubbleStrategy
syntax "bestFirst" : ibubbleStrategy
syntax "depthFirst" : ibubbleStrategy
syntax "breadthFirst" : ibubbleStrategy

/- Specify the normalization mode used by ibubble. -/
declare_syntax_cat ibubbleNormMode
syntax "simp" : ibubbleNormMode

/- Pure-goal behavior: either run a solver or stop after `ipureintro`. -/
declare_syntax_cat ibubblePureSolver
syntax "pureBy" tactic : ibubblePureSolver
syntax "pureStop" : ibubblePureSolver

/- Bound repeated uses of one theorem along a search branch. -/
declare_syntax_cat ibubbleTheoremLimit
syntax "maxTheoremUses" ppSpace num : ibubbleTheoremLimit

/- Bound search depth and, consequently, the normalization steps available to a goal. -/
declare_syntax_cat ibubbleDepthLimit
syntax "maxDepth" ppSpace num : ibubbleDepthLimit

/- Local rule edits for one `ibubble` invocation. -/
declare_syntax_cat ibubbleRuleDirection
syntax "backward" : ibubbleRuleDirection
syntax "forward" : ibubbleRuleDirection

declare_syntax_cat ibubbleLocalRule
syntax ibubbleRuleDirection ppSpace ident (ppSpace num "%")? : ibubbleLocalRule

declare_syntax_cat ibubbleErasedRule
syntax ibubbleRuleDirection ppSpace ident : ibubbleErasedRule

declare_syntax_cat ibubbleRuleEdit
syntax "with" "[" ibubbleLocalRule,* "]" : ibubbleRuleEdit
syntax "without" "[" ibubbleErasedRule,* "]" : ibubbleRuleEdit

syntax (name := ibubbleTactic)  "ibubble"
  (ppSpace ibubbleStrategy)? (ppSpace ibubbleNormMode)?
  (ppSpace ibubblePureSolver)? (ppSpace ibubbleTheoremLimit)?
  (ppSpace ibubbleDepthLimit)?
  (ppSpace ibubbleRuleEdit)* : tactic
syntax (name := ibubbleTactic?) "ibubble?"
  (ppSpace ibubbleStrategy)? (ppSpace ibubbleNormMode)?
  (ppSpace ibubblePureSolver)? (ppSpace ibubbleTheoremLimit)?
  (ppSpace ibubbleDepthLimit)?
  (ppSpace ibubbleRuleEdit)* : tactic

end Bubble
