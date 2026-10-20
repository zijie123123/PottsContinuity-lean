module

public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

private theorem mem_edgeRestrictionConfigurationEquiv_symm
    {V : Type*} {H : SimpleGraph V} (R : Configuration H)
    (A : RemainingConfiguration H R) (e : (edgeRestriction H R).edgeSet) :
    e ∈ (edgeRestrictionConfigurationEquiv H R).symm A ↔
      edgeRestrictionEdgeEmbedding H R e ∈ A.val := by
  have hv := congrArg Subtype.val
    ((edgeRestrictionConfigurationEquiv H R).apply_symm_apply A)
  rw [edgeRestrictionConfigurationEquiv_val] at hv
  constructor
  · intro he
    rw [← hv]
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  · intro he
    rw [← hv] at he
    rcases Finset.mem_map.mp he with ⟨f, hf, hfe⟩
    have hfe' : edgeRestrictionEdgeEmbedding H R f =
        edgeRestrictionEdgeEmbedding H R e := by
      simpa using hfe
    have hfe'' := (edgeRestrictionEdgeEmbedding H R).injective hfe'
    subst f
    exact hf

/-- The retained dual edge crossed by a primal subgraph edge. -/
noncomputable def rectangleSubgraphDualEdgeEmbedding
    {a : PD.FK.LatticeVertex} {w h : ℕ}
    {G : SimpleGraph (RectangleVertex a w h)}
    (hG : G ≤ rectangleGraph a w h) (g : G.edgeSet) :
    (rectangleSubgraphDualGraph hG).edgeSet := by
  classical
  let dHost := rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g)
  have hnot : dHost ∉ rectangleSubgraphRemovedDualEdges hG := by
    intro hd
    unfold rectangleSubgraphRemovedDualEdges at hd
    rcases Finset.mem_map.mp hd with ⟨f, hf, hfd⟩
    have hfd' : rectangleDualEdgeEquiv a w h f =
        rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g) := by
      change rectangleDualEdgeEquiv a w h f = dHost at hfd
      simpa only [dHost] using hfd
    have hfg : f = subgraphEdgeEmbedding hG g :=
      (rectangleDualEdgeEquiv a w h).injective hfd'
    have hnot' := (mem_subgraphRemovedEdges (G := G)
      (H := rectangleGraph a w h) f).mp hf
    apply hnot'
    rw [hfg]
    exact g.property
  exact ⟨dHost.1, by
    rw [rectangleSubgraphDualGraph, edgeRestriction_edgeSet]
    refine ⟨dHost.2, ?_⟩
    intro hd
    exact hnot ((coe_mem_openEdges_iff _ _ _).mp hd)⟩

/-- The retained dual graph edge has the endpoints of the actual crossed
dual bond of its source edge. -/
theorem rectangleSubgraphDualEdgeEmbedding_crossingBond
    {a : PD.FK.LatticeVertex} {w h : ℕ}
    {G : SimpleGraph (RectangleVertex a w h)}
    (hG : G ≤ rectangleGraph a w h) (g : G.edgeSet) :
    Sym2.map (fun z : RectangleDualVertex a w h => z.1)
        (rectangleSubgraphDualEdgeEmbedding hG g).val =
      (PD.FK.Medial.dualBondOfPrimal
        (rectanglePrimalEdgeBond a w h (subgraphEdgeEmbedding hG g))).toSym2 := by
  let d := rectanglePrimalDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g)
  have hval : (rectangleSubgraphDualEdgeEmbedding hG g).val =
      (rectangleDualGraphEdgeEquiv a w h d).val := rfl
  rw [hval]
  change s((rectangleDualEdgeSource a w h d).val,
      (rectangleDualEdgeTarget a w h d).val) = _
  rw [rectangleDualEdgeSource_faceBase, rectangleDualEdgeTarget_faceBase]
  simp [d, rectanglePrimalDualEdgeEquiv,
    PD.FK.Medial.LatticeBond.toSym2,
    PD.FK.Medial.dualBondOfPrimal_source,
    PD.FK.Medial.dualBondOfPrimal_target]

/-- In the finite dual configuration map for a rectangle subgraph, each
retained dual bond is open exactly when its crossed primal bond is closed. -/
theorem rectangleSubgraphDualConfigurationEquiv_edgeState
    {a : PD.FK.LatticeVertex} {w h : ℕ}
    {G : SimpleGraph (RectangleVertex a w h)}
    (hG : G ≤ rectangleGraph a w h) (C : Configuration G)
    (g : G.edgeSet) :
    rectangleSubgraphDualEdgeEmbedding hG g ∈
      rectangleSubgraphDualConfigurationEquiv hG C ↔ g ∉ C := by
  classical
  let : DecidableEq (rectangleDualGraph a w h).edgeSet :=
    PottsContinuity.DualityExt.subgraphDualDualEdgeDecidableEq
  let d := rectangleSubgraphDualEdgeEmbedding hG g
  change d ∈ (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
    (rectangleSubgraphRemovedDualEdges hG)).symm
      (rectangleSubgraphDualRemainingEquiv hG C) ↔ g ∉ C
  rw [mem_edgeRestrictionConfigurationEquiv_symm]
  have hval := congrArg Subtype.val
    (rectangleSubgraphDualRemainingEquiv_apply hG C)
  rw [hval]
  have hdHost : edgeRestrictionEdgeEmbedding (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG) d =
      rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g) := by
    apply Subtype.ext
    rfl
  rw [hdHost]
  change rectangleDualEdgeEquiv a w h (subgraphEdgeEmbedding hG g) ∈
      positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG C) \
          rectangleSubgraphRemovedDualEdges hG ↔ g ∉ C
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hfull, _⟩
    have hclosed := (rectangleDualEdgeEquiv_mem_dualConfiguration
      (subgraphConfigurationEmbedding hG C)
      (subgraphEdgeEmbedding hG g)).mp hfull
    intro hg
    apply hclosed
    exact Finset.mem_map.mpr ⟨g, hg, rfl⟩
  · intro hg
    constructor
    · exact (rectangleDualEdgeEquiv_mem_dualConfiguration
        (subgraphConfigurationEmbedding hG C)
        (subgraphEdgeEmbedding hG g)).mpr (by
          intro hmem
          have hmem' := (mem_subgraphConfigurationRestriction hG
            (subgraphConfigurationEmbedding hG C) g).mpr hmem
          rw [subgraphConfigurationRestriction_embedding] at hmem'
          exact hg hmem')
    · intro hd'
      unfold rectangleSubgraphRemovedDualEdges at hd'
      rcases Finset.mem_map.mp hd' with ⟨f, hf, hfd⟩
      have heq : f = subgraphEdgeEmbedding hG g :=
        (rectangleDualEdgeEquiv a w h).injective (by
          change rectangleDualEdgeEquiv a w h f = _ at hfd
          simpa using hfd)
      have hremoved := (mem_subgraphRemovedEdges (G := G)
        (H := rectangleGraph a w h) f).mp hf
      apply hremoved
      rw [heq]
      exact g.property

end

end PottsContinuity.DualityExt
