module

public import PottsContinuity.Thm3.Prop4.RectangleDeletedReferenceGraph
public import PottsContinuity.PD.Duality.RectangleDualAmbientMarginal

/-!
# Exact ambient marginal after deleting the crossed tube reveal

The expanded induced dual graph may contain extra boundary edges. Their
endpoints are already in the same exterior wired class, even after deleting
the genuine crossed reveal. Restriction therefore has the exact true dual
FK law, rather than merely a stochastic bound.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

private theorem prewired_subgraph_law {V : Type*} [Finite V]
    {G H : SimpleGraph V} (hGH : G ≤ H) (θ : Parameters) (ξ : BoundaryCondition V)
    (hpre : ∀ u v, H.Adj u v → ¬ G.Adj u v → ξ.partition.r u v) :
    (law H θ ξ).map (subgraphConfigurationRestriction hGH) = law G θ ξ := by
  classical
  let prewiredEdgesDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
  let R := subgraphRemovedEdges G H
  have hR : ∀ u v (huv : H.Adj u v),
      (⟨s(u,v),H.mem_edgeSet.mpr huv⟩ : H.edgeSet) ∈ R → ξ.partition.r u v := by
    intro u v huv he
    apply hpre u v huv
    intro hG
    exact (mem_subgraphRemovedEdges _).mp he (G.mem_edgeSet.mpr hG)
  have hremove := law_map_remove H θ ξ R hR
  have hsubgraph := law_subgraphRemaining_map hGH θ ξ
  calc
    (law H θ ξ).map (subgraphConfigurationRestriction hGH) =
        ((law H θ ξ).map (fun C => (configurationSplitEquiv H R C).1)).map
          (subgraphRemainingConfigurationEquiv hGH).symm := by
      rw [PMF.map_comp]
      congr 1
      funext C
      simpa only [Function.comp_apply,R] using
        (subgraphRemainingConfigurationEquiv_symm_split hGH C).symm
    _ = ((law G θ ξ).map (subgraphRemainingConfigurationEquiv hGH)).map
        (subgraphRemainingConfigurationEquiv hGH).symm := by rw [hremove,hsubgraph]
    _ = law G θ ξ := by
      rw [PMF.map_comp]
      have hc : ((subgraphRemainingConfigurationEquiv hGH).symm ∘
          subgraphRemainingConfigurationEquiv hGH) = id := by
        funext A
        exact Equiv.symm_apply_apply _ A
      rw [hc,PMF.map_id]

/-- Crossed revealed bonds embedded into the ordinary expanded induced graph. -/
def rectangleAmbientCrossedReveal (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) : Configuration (rectangleDualAmbientGraph a w h) :=
  subgraphConfigurationEmbedding (rectangleDualGraph_le_ambient a w h)
    (rectangleCrossedEdges a w h R)

/-- Deletion retains precisely the same geometric unordered bonds in the
true dual graph and its expanded induced ambient graph. -/
theorem rectangle_deleted_dual_le_ambient (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) :
    edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R) ≤
      edgeRestriction (rectangleDualAmbientGraph a w h) (rectangleAmbientCrossedReveal a w h R) := by
  have hopen := congrArg SimpleGraph.edgeSet
    (openGraph_subgraphConfigurationEmbedding (rectangleDualGraph_le_ambient a w h)
      (rectangleCrossedEdges a w h R))
  simp only [openGraph_edgeSet] at hopen
  change (rectangleDualGraph a w h).deleteEdges _ ≤ (rectangleDualAmbientGraph a w h).deleteEdges _
  change (rectangleDualGraph a w h).deleteEdges _ ≤
    (rectangleDualAmbientGraph a w h).deleteEdges (openEdges _
      (subgraphConfigurationEmbedding (rectangleDualGraph_le_ambient a w h) (rectangleCrossedEdges a w h R)))
  rw [hopen]
  exact SimpleGraph.deleteEdges_mono (rectangleDualGraph_le_ambient a w h)

/-- Adding the unsampled ambient boundary edges to the deleted reference
and restricting back leaves the exact FK law unchanged. -/
theorem rectangle_deleted_ambient_law_restrict (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (θ : Parameters) :
    (law (edgeRestriction (rectangleDualAmbientGraph a w h) (rectangleAmbientCrossedReveal a w h R))
      θ (rectangleDualBoundaryCondition a w h)).map
        (subgraphConfigurationRestriction (rectangle_deleted_dual_le_ambient a w h R)) =
      law (edgeRestriction (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R))
        θ (rectangleDualBoundaryCondition a w h) := by
  apply prewired_subgraph_law
  intro u v huv hnot
  simp only [edgeRestriction,SimpleGraph.deleteEdges_adj] at huv hnot
  have hopen := congrArg SimpleGraph.edgeSet
    (openGraph_subgraphConfigurationEmbedding (rectangleDualGraph_le_ambient a w h)
      (rectangleCrossedEdges a w h R))
  simp only [openGraph_edgeSet] at hopen
  have hA : (rectangleDualAmbientGraph a w h).Adj u v ∧
      s(u,v) ∉ openEdges (rectangleDualGraph a w h) (rectangleCrossedEdges a w h R) := by
    exact ⟨huv.1,by rw [← hopen]; exact huv.2⟩
  have hG : ¬ (rectangleDualGraph a w h).Adj u v := by
    intro hadj
    exact hnot ⟨hadj,hA.2⟩
  exact (rectangleDualBoundaryCondition_rel a w h u v).mpr
    (Or.inr (rectangleDualAmbient_extraEdge_endpoints_boundary a w h u v hA.1 hG))

end
end PottsContinuity.Thm3.Prop4
