module

public import PottsContinuity.Thm3.RSW.BottomCollarInducedDualLaw
public import PottsContinuity.PlanarMixed.Square.GeneralRectangleDualBottomCollarRestriction

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt PlanarMixed.Square
noncomputable section

/-- The existing coordinate inclusions of the original primal rectangle agree. -/
theorem bottomCollar_primal_embedding_eq (a : LatticeVertex) (w h : ℕ) :
    FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h =
      PlanarMixed.Square.rectangleArbitraryBottomCollarEmbedding a w h := by
  apply Function.Embedding.ext
  intro v
  rfl

/-- The complementary removed bonds are exactly the previously constructed
geometric dual collar bonds, on their original host-edge carrier. -/
theorem bottomCollar_removed_dual_eq (a : LatticeVertex) (w h : ℕ) :
    rectangleSubgraphRemovedDualEdges (bottomCollar_source_map_le a w h) =
      generalRectangleDualBottomCollarRemovedDualEdges a w h := by
  classical
  ext d
  obtain ⟨e,rfl⟩ := (rectangleDualEdgeEquiv (a.1,a.2-1) w (h+1)).surjective d
  have hl : rectangleDualEdgeEquiv (a.1,a.2-1) w (h+1) e ∈
      rectangleSubgraphRemovedDualEdges (bottomCollar_source_map_le a w h) ↔
      e ∈ subgraphRemovedEdges
        ((rectangleGraph a w h).map (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h))
        (rectangleGraph (a.1,a.2-1) w (h+1)) :=
    Finset.mem_map' (rectangleDualEdgeEquiv (a.1,a.2-1) w (h+1)).toEmbedding
  have hr := generalRectangleDualBottomCollar_removedDual_mem_iff a w h
    (rectanglePrimalDualEdgeEquiv (a.1,a.2-1) w (h+1) e)
  have hr' : rectangleDualEdgeEquiv (a.1,a.2-1) w (h+1) e ∈
      generalRectangleDualBottomCollarRemovedDualEdges a w h ↔
      e ∈ subgraphRemovedEdges
        ((rectangleGraph a w h).map (PlanarMixed.Square.rectangleArbitraryBottomCollarEmbedding a w h))
        (rectangleGraph (a.1,a.2-1) w (h+1)) := hr
  have hs := congrArg (fun f : RectangleVertex a w h ↪
      RectangleVertex (a.1,a.2-1) w (h+1) =>
      subgraphRemovedEdges ((rectangleGraph a w h).map f)
        (rectangleGraph (a.1,a.2-1) w (h+1)))
    (bottomCollar_primal_embedding_eq a w h)
  exact hl.trans ((Iff.of_eq (congrArg (fun S => e ∈ S) hs)).trans hr'.symm)

/-- The actual complementary sampled graph is the mapped inner true dual,
with the additional host vertices retained as isolated vertices. -/
theorem bottomCollar_residual_graph_eq_map_inner (a : LatticeVertex) (w h : ℕ) :
    bottomCollarInducedDualGraph a w h =
      (rectangleDualGraph a w h).map
        (generalRectangleDualBottomCollar_vertexEmbedding a w h) := by
  have hr : bottomCollarInducedDualGraph a w h =
      generalRectangleDualBottomCollarRemainingGraph a w h := by
    unfold bottomCollarInducedDualGraph rectangleSubgraphDualGraph
      generalRectangleDualBottomCollarRemainingGraph
    exact congrArg (edgeRestriction (rectangleDualGraph (a.1,a.2-1) w (h+1)))
      (bottomCollar_removed_dual_eq a w h)
  exact hr.trans (generalRectangleDualBottomCollar_remainingGraph_eq_map_inner a w h)

end
end PottsContinuity.RSW
