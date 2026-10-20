module

public import PottsContinuity.Thm3.Push.AuxiliaryLabelCut
public import PottsContinuity.DualityExt.PositiveRectangleSubgraphDuality
public import PottsContinuity.PD.Duality.RectangleDualCrossing
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- The auxiliary closed configuration is precisely the established true
rectangle dual configuration, on its original expanded face-base carrier. -/
theorem auxiliaryClosedConfiguration_rectangle_eq (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A =
      rectangleDualConfiguration a w h A := by
  classical
  ext f
  obtain ⟨g, rfl⟩ := (DualityExt.rectangleDualEdgeEquiv a w h).surjective f
  rw [mem_auxiliaryClosedConfiguration]
  simp only [Equiv.symm_apply_apply]
  change g ∉ A ↔ rectangleDualGraphEdgeEquiv a w h
    (rectanglePrimalDualEdgeEquiv a w h g) ∈ rectangleDualConfiguration a w h A
  exact (mem_rectangleDualConfiguration a w h A
    (rectanglePrimalDualEdgeEquiv a w h g)).symm

/-- Any label on the TRUE dual vertices which distinguishes all bottom and
top ports has an actual left-right primal cut crossing. Absence of the latter
would give a complementary dual path on which the label is constant. -/
theorem rectangle_dual_label_frontier_crosses (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleDualVertex a w h → Bool)
    (hbottom : ∀ b ∈ rectangleDualBottomPorts a w h, σ b = false)
    (htop : ∀ t ∈ rectangleDualTopPorts a w h, σ t = true) :
    auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h) σ ∈
      rectangleHorizontalCrossingEvent a w h := by
  by_contra hno
  obtain ⟨b, hb, t, ht, hconn⟩ :=
    rectangleDualBottomTop_of_no_primal_horizontal_crossing a w h _ hno
  rw [← auxiliaryClosedConfiguration_rectangle_eq] at hconn
  have hlabel := auxiliaryClosed_labelCut_reachable_preserves
    (DualityExt.rectangleDualEdgeEquiv a w h) σ hconn
  rw [hbottom b hb, htop t ht] at hlabel
  exact Bool.false_ne_true hlabel

end
end PottsContinuity.Push
