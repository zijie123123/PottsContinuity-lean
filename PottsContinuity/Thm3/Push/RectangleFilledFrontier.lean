module

public import PottsContinuity.Thm3.Push.FilledRegion
public import PottsContinuity.Thm3.Push.RectangleTopFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance filledTopPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance filledTopEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Dual vertices outside the reached top region which can reach a bottom
port without entering that region. Other complementary components are holes. -/
def rectangleBottomRegion (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Set (RectangleDualVertex a w h) :=
  outsideSeedRegion (rectangleDualGraph a w h)
    (rectangleTopReached a w h A) (rectangleDualBottomPorts a w h)

/-- The primal frontier after filling complementary components which do not
reach the bottom. This removes inner frontier components without opening a
single new sampled bond. -/
def rectangleFilledTopFrontier (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Configuration (rectangleGraph a w h) :=
  auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h)
    (fun v => decide (v ∉ rectangleBottomRegion a w h A))

theorem rectangleFilledTopFrontier_subset_original (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectangleFilledTopFrontier a w h A ⊆ rectangleTopFrontier a w h A :=
  filled_region_labelCut_subset _ _ _

/-- The filled frontier still consists entirely of OPEN recorded bonds. -/
theorem rectangleFilledTopFrontier_subset_open_and_revealed (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectangleFilledTopFrontier a w h A ⊆ A ∩ rectangleTopReveal a w h A :=
  (rectangleFilledTopFrontier_subset_original a w h A).trans
    (rectangleTopFrontier_subset_open_and_revealed a w h A)

/-- The entire bottom region is determined by the actual upper record. -/
theorem rectangleBottomRegion_eq_of_reveal_agreement (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hagree : B ∩ rectangleTopReveal a w h A = A ∩ rectangleTopReveal a w h A) :
    rectangleBottomRegion a w h B = rectangleBottomRegion a w h A := by
  apply congrArg (fun S => outsideSeedRegion (rectangleDualGraph a w h) S
    (rectangleDualBottomPorts a w h))
  exact closedClusterReached_eq_of_reveal_agreement _ _ A B hagree

end
end PottsContinuity.Push
