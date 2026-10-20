module

public import PottsContinuity.Thm3.Push.CutComponentPockets

@[expose] public section

namespace PottsContinuity.Push
open PlanarMixed

/-- Add exactly the components avoiding both designated seed sets to the
original closed one-sided exterior. No selector or stopping property is asserted. -/
def pocketAugmentedCutExterior {V : Type*} (G : SimpleGraph V)
    (cut left right : Set V) : Set V :=
  closedCutExterior G cut right ∪ (closedCutExterior G cut (left ∪ right))ᶜ

end PottsContinuity.Push
