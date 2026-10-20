module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightEmbeddingGeometry
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushReducedDefinitions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial DualityExt Thm4Side
noncomputable section

theorem rightNativeReduced_supported_bond (m : ℕ) (u w : NativeSideVertex m)
    (huw : (nativeSideReducedGraph m).Adj u w) (d : LatticeBond)
    (hd : d.toSym2 = s(u.val,w.val)) :
    (primalBondOfDual (rightNativeDualBond m d)).source ∈
      PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m) ∧
    (primalBondOfDual (rightNativeDualBond m d)).target ∈
      PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m) := by
  have hfull : (nativeSideFullGraph m).Adj u w := edgeRestriction_le _ _ huw
  have hnon : ¬ (u ∈ (nativeSideFullBoundary m).boundary ∧ w ∈ (nativeSideFullBoundary m).boundary) := by
    intro hboth
    have he := (nativeSideReducedGraph m).mem_edgeSet.mpr huw
    rw [nativeSideReducedGraph,edgeRestriction_edgeSet] at he
    apply he.2
    apply (coe_mem_openEdges_iff (nativeSideFullGraph m) (nativeSideWiredEdges m) ⟨s(u,w),(nativeSideFullGraph m).mem_edgeSet.mpr hfull⟩).mpr
    exact (mem_nativeSideWiredEdges_pair m u w hfull).mpr hboth
  have hsource : d.source ∈ PD.FK.latticeRectangle (-16*(m:ℤ)-1,0) (32*m+1) (15*m) := by
    rcases Sym2.eq_iff.mp hd with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact hs ▸ u.property
    · exact hs ▸ w.property
  have htarget : d.target ∈ PD.FK.latticeRectangle (-16*(m:ℤ)-1,0) (32*m+1) (15*m) := by
    rcases Sym2.eq_iff.mp hd with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact ht ▸ w.property
    · exact ht ▸ u.property
  have hnot : ¬ ((d.source.1 = -16*(m:ℤ)-1 ∨ d.source.1 = (16*m:ℤ) ∨ d.source.2 = (15*m:ℤ)) ∧
      (d.target.1 = -16*(m:ℤ)-1 ∨ d.target.1 = (16*m:ℤ) ∨ d.target.2 = (15*m:ℤ))) := by
    intro hb
    apply hnon
    change (u.val.1 = -16*(m:ℤ)-1 ∨ u.val.1 = (16*m:ℤ) ∨ u.val.2 = (15*m:ℤ)) ∧
      (w.val.1 = -16*(m:ℤ)-1 ∨ w.val.1 = (16*m:ℤ) ∨ w.val.2 = (15*m:ℤ))
    rcases Sym2.eq_iff.mp hd with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · change d.source = u.val at hs
      change d.target = w.val at ht
      rw [hs,ht] at hb
      exact hb
    · change d.source = w.val at hs
      change d.target = u.val at ht
      rw [hs,ht] at hb
      exact ⟨hb.2,hb.1⟩
  exact rightNative_primal_supported m d hsource htarget hnot

theorem rightNativeReduced_map_le_hostDual (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    (nativeSideReducedGraph m).map (rightNativeToHostDual m) ≤
      rectangleSubgraphDualGraph (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X)) := by
  intro z v hzv
  obtain ⟨u,w,huw,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hzv
  have hfull : (nativeSideFullGraph m).Adj u w := edgeRestriction_le _ _ huw
  obtain ⟨d,hd⟩ := LatticeBond.exists_of_adj hfull
  have hp := rightNativeReduced_supported_bond m u w huw d hd
  obtain ⟨e,he⟩ := right_retained_dual_edge_of_supported_primal m hm X
    (primalBondOfDual (rightNativeDualBond m d)) hp.1 hp.2
  have hep : e.val = s(rightNativeToHostDual m u,rightNativeToHostDual m w) := by
    apply Sym2.map.injective Subtype.val_injective
    rw [he,dualBondOfPrimal_primalBondOfDual,rightNativeDualBond_pair,hd]
    rfl
  apply (rectangleSubgraphDualGraph
    (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))).mem_edgeSet.mp
  rw [← hep]
  exact e.property

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
