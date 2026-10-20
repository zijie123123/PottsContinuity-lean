module

public import PottsContinuity.Thm3.Push.RectangleLabelFrontier
public import PottsContinuity.PD.Duality.RectangleCrossingExclusion
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance topFrontierPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance topFrontierEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Top-port closed-dual exploration, recorded on original primal bonds. -/
abbrev rectangleTopReveal (a : LatticeVertex) (w h : ℕ) :=
  closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) (rectangleDualTopPorts a w h)

/-- The actual closed-dual region reached from all top ports. -/
abbrev rectangleTopReached (a : LatticeVertex) (w h : ℕ) :=
  closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h) (rectangleDualTopPorts a w h)

/-- The entire canonical primal frontier of the reached top region. Keeping
all frontier bonds avoids making a non-unique choice of a crossing path. -/
def rectangleTopFrontier (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : Configuration (rectangleGraph a w h) :=
  auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h)
    (fun v => decide (v ∈ rectangleTopReached a w h A))

theorem rectangleTopReached_top (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {v : RectangleDualVertex a w h}
    (hv : v ∈ rectangleDualTopPorts a w h) : v ∈ rectangleTopReached a w h A :=
  ⟨v, hv, SimpleGraph.Reachable.rfl⟩

/-- An actual primal crossing prevents the top closed-dual exploration from
reaching any bottom port. Original open paths and true dual edges are used. -/
theorem rectangleTopReached_avoids_bottom (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    {b : RectangleDualVertex a w h} (hb : b ∈ rectangleDualBottomPorts a w h) :
    b ∉ rectangleTopReached a w h A := by
  rintro ⟨t, ht, htb⟩
  rw [auxiliaryClosedConfiguration_rectangle_eq] at htb
  have hby : b.val.2 = a.2-1 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    rfl
  have hty : t.val.2 = a.2+(h : ℤ) := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    rfl
  exact rectanglePrimalDualCrossings_exclusive a w h A hA ⟨b,t,hby,hty,htb.symm⟩

/-- The canonical frontier contains an actual left-right crossing whenever
the original configuration does. This is a proved separating barrier, not a
claim that the lower random domain contains a whole Euclidean rectangle. -/
theorem rectangleTopFrontier_crosses (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h) :
    rectangleTopFrontier a w h A ∈ rectangleHorizontalCrossingEvent a w h := by
  apply rectangle_dual_label_frontier_crosses
  · intro b hb
    exact decide_eq_false (rectangleTopReached_avoids_bottom a w h A hA hb)
  · intro t ht
    exact decide_eq_true (rectangleTopReached_top a w h A ht)

/-- Every canonical frontier bond is actually OPEN and recorded. -/
theorem rectangleTopFrontier_subset_open_and_revealed (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    rectangleTopFrontier a w h A ⊆ A ∩ rectangleTopReveal a w h A :=
  reached_labelCut_subset_open_and_revealed _ _ A

/-- The complete frontier is one-sided local to its concrete upper reveal. -/
theorem rectangleTopFrontier_eq_of_reveal_agreement (a : LatticeVertex) (w h : ℕ)
    (A B : Configuration (rectangleGraph a w h))
    (hagree : B ∩ rectangleTopReveal a w h A = A ∩ rectangleTopReveal a w h A) :
    rectangleTopFrontier a w h B = rectangleTopFrontier a w h A := by
  apply congrArg (auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h))
  funext v
  apply decide_eq_decide.mpr
  exact closedCluster_reached_iff_of_reveal_agreement _ _ A B hagree v

end
end PottsContinuity.Push
