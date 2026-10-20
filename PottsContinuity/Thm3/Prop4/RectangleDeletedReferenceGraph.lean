module

public import PottsContinuity.Thm3.Prop4.FrozenDualRemainingLaw
public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual

/-!
# The actual geometry of the deleted all-open reference

The complementary configuration of the whole reveal is exactly the retained
dual graph. Sampled walks lift to that same graph on the original finite
face carrier, without adding exterior cap edges.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance deletedReferenceDualEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _
local instance deletedReferenceDualEdgeFinite (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _

/-- Membership under the genuine crossing correspondence preserves the
original edge set, before taking the complementary dual state. -/
theorem rectangle_crossed_edge_mem_iff (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (e : (rectangleGraph a w h).edgeSet) :
    rectangleCrossingEdgeEquiv a w h e ∈ rectangleCrossedEdges a w h R ↔ e ∈ R := by
  change _ ∈ R.map (rectangleCrossingEdgeEquiv a w h).toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  rw [(rectangleCrossingEdgeEquiv a w h).symm_apply_apply e]

end
end PottsContinuity.Thm3.Prop4
