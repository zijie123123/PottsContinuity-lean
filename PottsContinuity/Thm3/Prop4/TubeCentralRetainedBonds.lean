module

public import PottsContinuity.Thm3.Prop4.TubeHalfPlaneEdges

/-!
# Retained vertical connectors outside the literal central cut

At every physical row outside the cut interval, the horizontal crossed
original bond is unrevealed. Its true dual bond survives in the reference
graph, including the rows adjacent to the two cut endpoints.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Exact reveal membership for a genuine horizontal bond in the central column. -/
theorem central_horizontal_revealed_iff_row (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (y : ℤ) (c : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (hc : c.val = ⟨(0,y),.horizontal⟩) :
    rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c ∈
      rectangleTubeRevealedEdges n r u v ↔ y ∈ radiusTubeCutRows n r u v 0 := by
  rw [rectangle_bond_mem_tube_reveal_iff, hc]
  exact (mem_radiusTubeCutRows_iff n r u v 0 y).symm

end
end PottsContinuity.Thm3.Prop4
