module

public import PottsContinuity.Thm4SideEuler.ResidualHostDualLaw
public import PottsContinuity.DualityExt.PositiveSubgraphDualEdgeEquiv
public import PottsContinuity.DualityExt.PositiveWiredDualEdgeState

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial DualityExt Thm4Side
noncomputable section

def rightSourceBondVertex (m : ℕ) (z : LatticeVertex)
    (hz : z ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m)) :
    FKC.FiniteFK.SlitBoxVertex (16*m) :=
  ⟨z,by
    have hb := (PD.FK.mem_latticeRectangle _ z _ _).mp hz
    rw [FKC.mem_latticeRectangle]
    push_cast at hb ⊢
    constructor <;> constructor <;> omega⟩

def rightSourceBondEdge (m : ℕ) (hm : 1 ≤ m) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (ht : b.target ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m)) :
    (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := by
  let u := rightSourceBondVertex m b.source hs
  let v := rightSourceBondVertex m b.target ht
  refine ⟨s(u,v),(FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr ?_⟩
  apply (FKC.FiniteFK.slitBoxGraph_adj_iff (16*m) u v).mpr
  refine ⟨(PD.FK.squareLattice_adj_iff _ _).mp b.adjacent,?_⟩
  rintro ⟨hu,hv⟩
  have h := (PD.FK.mem_latticeRectangle _ b.source _ _).mp hs
  have hu0 : b.source.1=0 := hu.1
  omega

theorem rightSourceBondEdge_not_revealed (m : ℕ) (hm : 1 ≤ m) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (ht : b.target ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    rightSourceBondEdge m hm b hs ht ∉ slitRightDualRectangleReveal m X := by
  rw [slitRightDualRectangleReveal]
  apply (slitRightHalfReveal_complement_edge_iff m _).mpr
  intro z hz
  unfold rightSourceBondEdge at hz
  change z ∈ s(rightSourceBondVertex m b.source hs,rightSourceBondVertex m b.target ht) at hz
  rcases (Sym2.mem_iff').mp hz with rfl | rfl
  · exact ((PD.FK.mem_latticeRectangle _ b.source _ _).mp hs).1.1
  · exact ((PD.FK.mem_latticeRectangle _ b.target _ _).mp ht).1.1

theorem right_retained_dual_edge_of_supported_primal (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m))
    (ht : b.target ∈ PD.FK.latticeRectangle ((m:ℤ),-(16*m:ℤ)) (15*m) (32*m)) :
    ∃ d : (rectangleSubgraphDualGraph
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))).edgeSet,
      Sym2.map (fun z : RectangleDualVertex
        (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) => z.val) d.val =
        (dualBondOfPrimal b).toSym2 := by
  classical
  let R := slitRightDualRectangleReveal m X
  let G := FKC.FiniteFK.slitBoxGraph (16*m)
  let J := edgeRestriction G R
  let A := positiveActiveGraph J
  let c := rightSourceBondEdge m hm b hs ht
  have hc : c.val ∈ J.edgeSet := by
    rw [edgeRestriction_edgeSet]
    exact ⟨c.property,by
      intro h
      exact rightSourceBondEdge_not_revealed m hm b hs ht X ((coe_mem_openEdges_iff G R c).mp h)⟩
  let cJ : J.edgeSet := ⟨c.val,hc⟩
  let cA := (positiveActiveEdgeToGraphEquiv J).symm cJ
  let f := sideExactLawHostEmbedding m R
  let cM := isolatedExtensionEdgeEquiv A f cA
  let hG := sideExactLawHostSubgraph_le m R
  let d := rectangleSubgraphDualEdgeEquiv hG cM
  refine ⟨d,?_⟩
  have hp := rectangleSubgraphDualEdgeEquiv_crossingBond hG cM
  have hnorm : rectanglePrimalEdgeBond _ _ _ (subgraphEdgeEmbedding hG cM) = b := by
    apply LatticeBond.toSym2_injective
    have hpair := congrArg Subtype.val (wholePlaneBondEdgeEquiv.apply_symm_apply
      (rectanglePrimalEdgeToSquareEdge _ _ _ (subgraphEdgeEmbedding hG cM)))
    change (rectanglePrimalEdgeBond _ _ _ (subgraphEdgeEmbedding hG cM)).toSym2 =
      Sym2.map (fun z : sideExactLawHostVertex (16*m) => z.val) cM.val at hpair
    rw [hpair]
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
  simpa only [hnorm] using hp

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
