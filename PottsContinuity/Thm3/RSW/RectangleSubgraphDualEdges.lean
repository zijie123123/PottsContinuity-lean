module

public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

variable {a : LatticeVertex} {w h : ℕ} {G : SimpleGraph (RectangleVertex a w h)}

/-- The dual of a retained source edge is not a removed dual edge. -/
theorem rectangleSubgraph_sourceDual_not_removed (hG : G ≤ rectangleGraph a w h)
    (e : G.edgeSet) :
    rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e) ∉
      rectangleSubgraphRemovedDualEdges hG := by
  intro he
  obtain ⟨d,hd,hde⟩ := Finset.mem_map.mp he
  have heq := (rectangleDualEdgeEquiv a w h).injective hde
  subst d
  exact (mem_subgraphRemovedEdges _).mp hd e.property

/-- The actual complementary sampled edge, retaining its original face pair. -/
def rectangleSubgraphSourceDualEdge (hG : G ≤ rectangleGraph a w h)
    (e : G.edgeSet) : (rectangleSubgraphDualGraph hG).edgeSet :=
  (edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
    (rectangleSubgraphRemovedDualEdges hG)).symm
      ⟨rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e),
        rectangleSubgraph_sourceDual_not_removed hG e⟩

/-- A retained dual edge has a unique original source edge, not a deleted bond. -/
def rectangleSubgraphDualSourceEdge (hG : G ≤ rectangleGraph a w h)
    (e : (rectangleSubgraphDualGraph hG).edgeSet) : G.edgeSet := by
  let d := edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
    (rectangleSubgraphRemovedDualEdges hG) e
  let p := (rectangleDualEdgeEquiv a w h).symm d.val
  refine ⟨p.val,?_⟩
  by_contra hp
  have hremoved : p ∈ subgraphRemovedEdges G (rectangleGraph a w h) :=
    (mem_subgraphRemovedEdges p).mpr hp
  apply d.property
  exact Finset.mem_map.mpr ⟨p,hremoved,(rectangleDualEdgeEquiv a w h).apply_symm_apply d.val⟩

/-- The source and residual-dual sampled edges are in exact complementary
bijection, including the original unordered endpoint pairs on both sides. -/
def rectangleSubgraphSourceDualEdgeEquiv (hG : G ≤ rectangleGraph a w h) :
    G.edgeSet ≃ (rectangleSubgraphDualGraph hG).edgeSet where
  toFun := rectangleSubgraphSourceDualEdge hG
  invFun := rectangleSubgraphDualSourceEdge hG
  left_inv e := by
    apply Subtype.ext
    change ((rectangleDualEdgeEquiv a w h).symm
      (((edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
        (rectangleSubgraphRemovedDualEdges hG))
        ((edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
          (rectangleSubgraphRemovedDualEdges hG)).symm _)).val)).val = e.val
    rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
    rfl
  right_inv e := by
    apply (edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG)).injective
    apply Subtype.ext
    change rectangleDualEdgeEquiv a w h
      (subgraphEdgeEmbedding hG (rectangleSubgraphDualSourceEdge hG e)) = _
    change rectangleDualEdgeEquiv a w h
      ((rectangleDualEdgeEquiv a w h).symm
        (edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
          (rectangleSubgraphRemovedDualEdges hG) e).val) = _
    exact Equiv.apply_symm_apply _ _

/-- Host inclusion of the retained dual edge gives exactly the complementary
edge of the original included source bond. -/
theorem rectangleSubgraphSourceDualEdge_host (hG : G ≤ rectangleGraph a w h)
    (e : G.edgeSet) :
    edgeRestrictionEdgeEmbedding (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG) (rectangleSubgraphSourceDualEdge hG e) =
    rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e) := by
  change ((edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
    (rectangleSubgraphRemovedDualEdges hG))
    ((edgeRestrictionEdgeEquiv (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG)).symm _)).val = _
  rw [Equiv.apply_symm_apply]

/-- Exact complementary state of each original retained sampled edge. -/
theorem rectangleSubgraphSourceDualEdge_mem (hG : G ≤ rectangleGraph a w h)
    (A : Configuration G) (e : G.edgeSet) :
    rectangleSubgraphSourceDualEdge hG e ∈ rectangleSubgraphDualConfigurationEquiv hG A ↔
      e ∉ A := by
  have hremain : edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG) (rectangleSubgraphDualConfigurationEquiv hG A) =
      rectangleSubgraphDualRemainingEquiv hG A := by
    exact Equiv.apply_symm_apply _ _
  have hmem : rectangleSubgraphSourceDualEdge hG e ∈ rectangleSubgraphDualConfigurationEquiv hG A ↔
      rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG e) ∈
        (rectangleSubgraphDualRemainingEquiv hG A).val := by
    rw [← hremain,edgeRestrictionConfigurationEquiv_val,
      ← rectangleSubgraphSourceDualEdge_host hG e,Finset.mem_map']
  rw [hmem,rectangleSubgraphDualRemainingEquiv_apply]
  simp only [configurationSplitEquiv,Equiv.coe_fn_mk,Finset.mem_sdiff,
    rectangleSubgraph_sourceDual_not_removed,not_false_eq_true,and_true]
  rw [rectangleDualEdgeEquiv_mem_dualConfiguration]
  exact not_congr (Finset.mem_map' (subgraphEdgeEmbedding hG))

end
end PottsContinuity.RSW
