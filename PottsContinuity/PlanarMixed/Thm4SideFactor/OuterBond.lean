module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.OuterSupport
public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightEmbeddingGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm4Side
noncomputable section

/-- An exterior primal bond produces an actually open removed dual bond. -/
theorem side_outer_dual_bond_open (m : ℕ)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (H : RemovedConfiguration (sideExactLawHostGraph (16*m))
      (subgraphRemovedEdges ((positiveActiveGraph (sideExactLawResidual m R)).map
        (sideExactLawHostEmbedding m R)) (sideExactLawHostGraph (16*m))))
    (hH : ∀ (c : (sideExactLawHostGraph (16*m)).edgeSet), c ∈ H.val →
      ∀ (z : sideExactLawHostVertex (16*m)), z ∈ c.val →
        z.val ∈ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
          (2*(16*m)) (2*(16*m)))
    (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)))
    (ht : b.target ∈ PD.FK.latticeRectangle
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)))
    (hout : b.source ∉ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
        (2*(16*m)) (2*(16*m)) ∨
      b.target ∉ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
        (2*(16*m)) (2*(16*m))) :
    ∃ d : (rectangleDualGraph
        (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1))).edgeSet,
      d ∈ (rectangleSubgraphDualOpenRemovedState (sideExactLawHostSubgraph_le m R) H).val ∧
      Sym2.map (fun z : RectangleDualVertex
        (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) => z.val) d.val =
        (dualBondOfPrimal b).toSym2 := by
  classical
  let u : sideExactLawHostVertex (16*m) := ⟨b.source,hs⟩
  let v : sideExactLawHostVertex (16*m) := ⟨b.target,ht⟩
  let c : (sideExactLawHostGraph (16*m)).edgeSet :=
    ⟨s(u,v),(sideExactLawHostGraph (16*m)).mem_edgeSet.mpr b.adjacent⟩
  have hu : u ∈ c.val := by simp [c]
  have hv : v ∈ c.val := by simp [c]
  have hc : c ∈ subgraphRemovedEdges
      ((positiveActiveGraph (sideExactLawResidual m R)).map (sideExactLawHostEmbedding m R))
      (sideExactLawHostGraph (16*m)) := by
    apply (mem_subgraphRemovedEdges c).mpr
    intro hmap
    rcases hout with hs | ht
    · exact hs (sideHost_mapped_endpoint_original m R c hmap u hu)
    · exact ht (sideHost_mapped_endpoint_original m R c hmap v hv)
  have hclosed : c ∉ H.val := by
    intro hcH
    rcases hout with hs | ht
    · exact hs (hH c hcH u hu)
    · exact ht (hH c hcH v hv)
  let E := rectangleDualEdgeEquiv
    (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1))
  let d := E c
  refine ⟨d,?_,?_⟩
  · have hrem : d ∈ rectangleSubgraphRemovedDualEdges (sideExactLawHostSubgraph_le m R) :=
      Finset.mem_map.mpr ⟨c,hc,rfl⟩
    have hn : d ∉ H.val.map E.toEmbedding := by
      intro hd
      obtain ⟨a,ha,had⟩ := Finset.mem_map.mp hd
      exact hclosed (E.injective had ▸ ha)
    simpa only [rectangleSubgraphDualOpenRemovedState,Finset.mem_sdiff] using And.intro hrem hn
  · let e := rectanglePrimalDualEdgeEquiv
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) c
    have hnorm : rectanglePrimalEdgeBond _ _ _ c = b := by
      apply LatticeBond.toSym2_injective
      have hp := congrArg Subtype.val (wholePlaneBondEdgeEquiv.apply_symm_apply
        (rectanglePrimalEdgeToSquareEdge _ _ _ c))
      exact hp
    change s((rectangleDualEdgeSource _ _ _ e).val,(rectangleDualEdgeTarget _ _ _ e).val) = _
    rw [rectangleDualEdgeSource_faceBase,rectangleDualEdgeTarget_faceBase]
    change s((rectanglePrimalEdgeBond _ _ _ c).faceBase false,
      (rectanglePrimalEdgeBond _ _ _ c).faceBase true) = _
    rw [hnorm]
    simp [LatticeBond.toSym2,dualBondOfPrimal_source,dualBondOfPrimal_target]

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
