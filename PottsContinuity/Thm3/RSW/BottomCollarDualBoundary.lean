module

public import PottsContinuity.Thm3.RSW.BottomCollarInducedDualLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

/-- An all-open primal collar forces every complementary removed dual bond
closed. No additional open dual bond enters the induced partition. -/
theorem bottomCollar_dual_openRemoved_empty (a : LatticeVertex) (w h : ℕ) :
    (rectangleSubgraphDualOpenRemovedState (bottomCollar_source_map_le a w h)
      (bottomCollarSourceState a w h)).val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  simp only [rectangleSubgraphDualOpenRemovedState,rectangleSubgraphRemovedDualEdges,
    bottomCollarSourceState,Finset.mem_sdiff] at he
  exact he.2 he.1

/-- The induced target partition is exactly the host dual exterior partition.
Isolated collar vertices remain on the carrier throughout this equality. -/
theorem bottomCollarInducedDualBoundary_partition (a : LatticeVertex) (w h : ℕ) :
    (bottomCollarInducedDualBoundary a w h).partition =
      (rectangleDualBoundaryCondition (a.1,a.2-1) w (h+1)).partition := by
  change componentSetoid _ _ (rectangleSubgraphDualOpenRemovedState
    (bottomCollar_source_map_le a w h) (bottomCollarSourceState a w h)).val = _
  rw [bottomCollar_dual_openRemoved_empty,componentSetoid_empty]

/-- The bottom-wired rectangle maps exactly to the residual complementary
sampled graph with the explicit host exterior wiring, for every real q>=1. -/
theorem bottomCollar_dual_law_at_selfDual (q : Set.Ici (1:ℝ))
    (a : LatticeVertex) (w h : ℕ) :
    (law (rectangleGraph a w h) (selfDualParameters q)
      (BoundaryCondition.wired {v : RectangleVertex a w h | v.val.2 = a.2})).map
      (bottomCollarInducedDualEquiv a w h) =
    law (bottomCollarInducedDualGraph a w h) (selfDualParameters q)
      (rectangleDualBoundaryCondition (a.1,a.2-1) w (h+1)) := by
  rw [bottomCollar_induced_dual_law_at_selfDual]
  exact law_eq_of_boundary_partition_eq _ _ _ (bottomCollarInducedDualBoundary_partition a w h)

end
end PottsContinuity.RSW
