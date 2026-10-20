module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightSourceBonds
public import PottsContinuity.Thm4SideEuler.HostDualDomination

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial DualityExt Thm4Side Thm4SideEuler
noncomputable section

theorem rightHostDual_edgeState (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (ht : b.target ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (d : (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))).edgeSet)
    (hd : Sym2.map (fun z : RectangleDualVertex
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) => z.val) d.val =
        (dualBondOfPrimal b).toSym2) :
    d ∈ slitRightResidualToHostDual m X
      ((configurationSplitEquiv (FKC.FiniteFK.slitBoxGraph (16*m))
        (slitRightDualRectangleReveal m X) Y).1) ↔
      rightSourceBondEdge m hm b hs ht ∉ Y := by
  classical
  let R := slitRightDualRectangleReveal m X
  let G := FKC.FiniteFK.slitBoxGraph (16*m)
  let J := edgeRestriction G R
  let A := positiveActiveGraph J
  let c := rightSourceBondEdge m hm b hs ht
  have hcR : c ∉ R := rightSourceBondEdge_not_revealed m hm b hs ht X
  have hc : c.val ∈ J.edgeSet := by
    rw [edgeRestriction_edgeSet]
    exact ⟨c.property,by intro h; exact hcR ((coe_mem_openEdges_iff G R c).mp h)⟩
  let cJ : J.edgeSet := ⟨c.val,hc⟩
  let cA := (positiveActiveEdgeToGraphEquiv J).symm cJ
  let f := sideExactLawHostEmbedding m R
  let cM := isolatedExtensionEdgeEquiv A f cA
  let hG := sideExactLawHostSubgraph_le m R
  let dc := rectangleSubgraphDualEdgeEquiv hG cM
  have hnorm : rectanglePrimalEdgeBond _ _ _ (subgraphEdgeEmbedding hG cM) = b := by
    apply LatticeBond.toSym2_injective
    have hp := congrArg Subtype.val (wholePlaneBondEdgeEquiv.apply_symm_apply
      (rectanglePrimalEdgeToSquareEdge _ _ _ (subgraphEdgeEmbedding hG cM)))
    change (rectanglePrimalEdgeBond _ _ _ (subgraphEdgeEmbedding hG cM)).toSym2 =
      Sym2.map (fun z : sideExactLawHostVertex (16*m) => z.val) cM.val at hp
    rw [hp]
    have hca := (positiveActiveEdgeToGraphEquiv J).apply_symm_apply cJ
    have hphys := congrArg (fun e : J.edgeSet =>
      Sym2.map (fun z : FKC.FiniteFK.SlitBoxVertex (16*m) => z.val) e.val) hca
    have hpairActive (e : (positiveActiveGraph J).edgeSet) :
        (positiveActiveEdgeToGraphEquiv J e).val = Sym2.map Subtype.val e.val := by rfl
    rw [hpairActive,Sym2.map_map] at hphys
    change Sym2.map (fun z : positiveActiveVertexSet J => z.val.val) cA.val = b.toSym2 at hphys
    change Sym2.map (fun z : sideExactLawHostVertex (16*m) => z.val) (Sym2.map f cA.val) = _
    rw [Sym2.map_map]
    exact hphys
  have hdc : dc = d := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    have hp := rectangleSubgraphDualEdgeEquiv_crossingBond hG cM
    rw [hnorm] at hp
    exact hp.trans hd.symm
  let B := (configurationSplitEquiv G R Y).1
  let C := (edgeRestrictionConfigurationEquiv G R).symm B
  let CA := (positiveActiveConfigurationEquiv J).symm C
  have hCA : cA ∈ CA ↔ cJ ∈ C := by
    have he := positiveActiveConfigurationEquiv_edgeState J CA cA
    have hback : positiveActiveConfigurationEquiv J CA = C :=
      (positiveActiveConfigurationEquiv J).apply_symm_apply C
    rw [hback] at he
    have hcback : positiveActiveEdgeToGraphEquiv J cA = cJ :=
      (positiveActiveEdgeToGraphEquiv J).apply_symm_apply cJ
    rw [hcback] at he
    exact he.symm
  have hCY : cJ ∈ C ↔ c ∈ Y := by
    have hbval : (edgeRestrictionConfigurationEquiv G R C).val = B.val :=
      congrArg Subtype.val ((edgeRestrictionConfigurationEquiv G R).apply_symm_apply B)
    rw [edgeRestrictionConfigurationEquiv_val] at hbval
    have hs : edgeRestrictionEdgeEmbedding G R cJ ∈ C.map (edgeRestrictionEdgeEmbedding G R) ↔ cJ ∈ C := by simp
    rw [hbval] at hs
    have hstate : cJ ∈ C ↔ c ∈ B.val := hs.symm
    exact hstate.trans (by change c ∈ Y \ R ↔ c ∈ Y; simp [hcR])
  rw [← hdc]
  change dc ∈ rectangleSubgraphDualConfigurationEquiv hG
    (isolatedExtensionConfigurationEquiv A f CA) ↔ _
  have he := embeddedRectangleSubgraphDualConfiguration_edgeState
    (W := sideExactLawHostVertex (16*m)) f hG CA cA
  exact he.trans (not_congr (hCA.trans hCY))

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
