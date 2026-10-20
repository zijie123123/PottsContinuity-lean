module

public import PottsContinuity.Thm3.RSW.BottomCollarResidualIdentification
public import PottsContinuity.PlanarMixed.Square.GeneralRectangleDualBottomCollarBoundary
public import PottsContinuity.PlanarMixed.Square.Extras

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarMixed.Square
noncomputable section

/-- The inner true dual embeds into the actual residual collar graph. -/
theorem bottomCollar_inner_map_le (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualGraph a w h).map (generalRectangleDualBottomCollar_vertexEmbedding a w h) ≤
      bottomCollarInducedDualGraph a w h :=
  (bottomCollar_residual_graph_eq_map_inner a w h).ge

/-- The outer exterior partition pulls back to exactly the inner three sides. -/
theorem bottomCollar_inner_partition (a : LatticeVertex) (w h : ℕ) :
    (isolatedExtensionPullbackBoundary (generalRectangleDualBottomCollar_vertexEmbedding a w h)
      (rectangleDualBoundaryCondition (a.1,a.2-1) w (h+1))).partition =
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h)).partition := by
  apply Setoid.ext
  intro u v
  exact generalRectangleDualBottomCollar_outerBoundaryCondition_pullback a w h u v

/-- Discarding only the isolated host collar vertices gives the exact inner
three-side-wired true-dual law at every admissible parameter. -/
theorem bottomCollar_inner_law_map (a : LatticeVertex) (w h : ℕ) (θ : Parameters) :
    (law (bottomCollarInducedDualGraph a w h) θ
      (rectangleDualBoundaryCondition (a.1,a.2-1) w (h+1))).map
      (embeddedConfigurationRestriction (rectangleDualGraph a w h)
        (bottomCollarInducedDualGraph a w h)
        (generalRectangleDualBottomCollar_vertexEmbedding a w h)
        (bottomCollar_inner_map_le a w h)) =
    law (rectangleDualGraph a w h) θ
      (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h)) := by
  apply law_embeddedConfigurationRestriction_eq_of_frozen_partition
  intro K
  have hK : K.val = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hn := (mem_subgraphRemovedEdges e).mp (K.property he)
    have hg := congrArg SimpleGraph.edgeSet (bottomCollar_residual_graph_eq_map_inner a w h)
    exact hn (Eq.mp (congrArg (fun S => e.val ∈ S) hg) e.property)
  change Setoid.comap _ (componentSetoid _ _ K.val) = _
  rw [hK,componentSetoid_empty]
  exact bottomCollar_inner_partition a w h

end
end PottsContinuity.RSW
