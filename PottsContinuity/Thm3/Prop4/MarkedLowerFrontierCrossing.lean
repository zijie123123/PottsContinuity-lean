module

public import PottsContinuity.Thm3.Prop4.MarkedLowerDualReveal

/-! # The prescribed marked lower frontier in the actual original sample -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance markedLowerFrontierEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The original-edge frontier of the actual lower-arc closed-dual reveal,
with both source mark heights retained. -/
def markedLowerFrontier (a : LatticeVertex) (w h : ℕ) (u v : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h)) : Configuration (rectangleGraph a w h) :=
  recordedDualFaceFrontier a w h (markedLowerDualReveal a w h u.val v.val A)
    (A ∩ markedLowerDualReveal a w h u.val v.val A)
    (PlanarTopology.rectangleLowerDualArc a w h u.val v.val)

end
end PottsContinuity.Thm3.Prop4
