module

public import PottsContinuity.Thm3.Prop4.RectangleSampledDualBridge
public import PottsContinuity.Thm3.Prop4.RecordedDualFaceFrontier

/-!
# The actual closed-dual lower-arc reveal with prescribed marks

The original-state reveal specializes the proved multi-seed cluster
exploration. Its seeds are the literal sampled lower complementary arc,
cut separately at the two prescribed primal mark heights.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance markedLowerDualVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _
local instance markedLowerDualRevealEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The literal finite lower complementary seed faces for the two marks. -/
def markedLowerDualSeeds (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex) :
    Finset (RectangleDualVertex a w h) := by
  classical
  exact Finset.univ.filter fun s => s.val ∈ PlanarTopology.rectangleLowerDualArc a w h u v

/-- All original bonds incident to the actual closed-dual region reached
from the prescribed lower arc. This is the raw region reveal before filling. -/
def markedLowerDualReveal (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A : Configuration (rectangleGraph a w h)) : Configuration (rectangleGraph a w h) :=
  Push.closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h)
    (markedLowerDualSeeds a w h u v) A

/-- The marked raw region reveal is an actual original-state stopping set. -/
theorem markedLowerDualReveal_stable (a : LatticeVertex) (w h : ℕ) (u v : LatticeVertex)
    (A C : Configuration (rectangleGraph a w h))
    (hagree : C ∩ markedLowerDualReveal a w h u v A = A ∩ markedLowerDualReveal a w h u v A) :
    markedLowerDualReveal a w h u v C = markedLowerDualReveal a w h u v A := by
  exact Push.closedClusterReveal_stable _ _ A C hagree

end
end PottsContinuity.Thm3.Prop4
