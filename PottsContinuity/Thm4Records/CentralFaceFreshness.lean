module

public import PottsContinuity.Thm4Records.QueriedScreenIndex

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.FK.Medial PD.Duality Exploration Push RSW Thm4Plane
noncomputable section

/-- Both full middle-face endpoints put the crossed original bond in the
literal R-star source carrier. -/
theorem crossedMiddleBond_mem_rStarSourceEdges (m : ℕ) (hm : 1 ≤ m)
    (d : FKC.Medial.LatticeBond)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (hcross : FKC.Medial.latticeBondEdge (FKC.Medial.primalBondOfDual d)=
      FKC.FiniteFK.slitBoxEdgeEmbedding (16*m) e)
    (hs : d.source ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (ht : d.target ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m) :
    e ∈ rStarSourceEdges m hm := by
  classical
  have hvertex (z : FKC.LatticeVertex) (hz : z ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m) :
      z ∈ PD.FK.latticeRectangle (slitScreenRStarBase m) (slitScreenRStarSide m)
        (slitScreenRStarSide m) := by
    simp only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc] at hz
    rw [PD.FK.mem_latticeRectangle]
    dsimp [slitScreenRStarBase,slitScreenRStarSide]
    constructor <;> constructor <;> omega
  let u : SlitRStarVertex m := ⟨d.source,hvertex _ hs⟩
  let v : SlitRStarVertex m := ⟨d.target,hvertex _ ht⟩
  have hadj : (SlitRStarGraph m).Adj u v :=
    (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr
      ((PD.FK.squareLattice_adj_iff _ _).mpr ((FKC.squareLattice_adj_iff _ _).mp d.adjacent))
  let f : (SlitRStarGraph m).edgeSet := ⟨s(u,v),(SlitRStarGraph m).mem_edgeSet.mpr hadj⟩
  have hd : (slitRStarEdgeBridge m hm f).dualBond=d := by
    apply FKC.Medial.LatticeBond.toSym2_injective
    exact (slitRStarEdgeBridge m hm f).pairEq
  have he : (slitRStarEdgeBridge m hm f).primalEdge=e := by
    apply (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m)).injective
    rw [← (slitRStarEdgeBridge m hm f).crosses,hd,hcross]
  simpa only [rStarSourceEdges,Finset.mem_image,Finset.mem_univ,true_and] using
    (show ∃ f : (SlitRStarGraph m).edgeSet, (slitRStarEdgeBridge m hm f).primalEdge=e from ⟨f,he⟩)

/-- No original query touches a dual face off both full screen traces in
the central index region. This is freshness for the actual residual carrier. -/
theorem centralFace_crossedBond_unqueried (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    {lb lt rb rt : FKC.LatticeVertex}
    (pL : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
      (sideFaceBases m false)).Walk lb lt)
    (pR : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
      (sideFaceBases m true)).Walk rb rt)
    (hlF : lb ∈ sideFaceBases m false) (hrF : rb ∈ sideFaceBases m true)
    (hlb : lb.2=-(16*(m:ℤ))-1) (hlt : lt.2=16*(m:ℤ))
    (hrb : rb.2=-(16*(m:ℤ))-1) (hrt : rt.2=16*(m:ℤ))
    (d : FKC.Medial.LatticeBond)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (hcross : FKC.Medial.latticeBondEdge (FKC.Medial.primalBondOfDual d)=
      FKC.FiniteFK.slitBoxEdgeEmbedding (16*m) e)
    (hd : d.source ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m ∧
      d.target ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (z : FKC.LatticeVertex) (hz : z ∈ d.toSym2)
    (hzL : z ∉ pL.support) (hzR : z ∉ pR.support)
    (hidxL : rayIndex z (sourceScreenIndexWalk m A (sideFaceBases m false) pL)=0)
    (hidxR : rayIndex z (sourceScreenIndexWalk m A (sideFaceBases m true) pR)=1) :
    e ∉ connectorReveal m hm A := by
  intro he
  obtain ⟨right,hr⟩ := queriedRStarEdge_side_query m hm A e
    (crossedMiddleBond_mem_rStarSourceEdges m hm d e hcross hd.1 hd.2) he
  have hzF : z ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m := by
    rcases Sym2.mem_iff'.mp hz with rfl | rfl
    · exact hd.1
    · exact hd.2
  have hcoords := hzF
  simp only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc] at hcoords
  have hzface : z ∈ (FKC.Medial.dualBondOfPrimal (FKC.Medial.primalBondOfDual d)).toSym2 := by
    rw [FKC.Medial.dualBondOfPrimal_primalBondOfDual]
    exact hz
  cases right
  · have hid := sideQuery_face_exteriorIndex m false A pL hlF hlb hlt e hr
      (FKC.Medial.primalBondOfDual d) hcross z hzface hzL ⟨by omega,by omega⟩
    simp only [Bool.false_eq_true,ite_false] at hid
    omega
  · have hid := sideQuery_face_exteriorIndex m true A pR hrF hrb hrt e hr
      (FKC.Medial.primalBondOfDual d) hcross z hzface hzR ⟨by omega,by omega⟩
    simp only [ite_true] at hid
    omega

end
end PottsContinuity.Thm4Records
