module

public import PottsContinuity.Thm4Records.SourceScreenIndex
public import PottsContinuity.Thm4Records.NativeCoordinates

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.FK.Medial PD.Duality Exploration Push RSW Thm4Plane
noncomputable section

/-- A queried original R-star bond comes from one of the two side clusters.
The local root observation and the frozen exterior are disjoint from it. -/
theorem queriedRStarEdge_side_query (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (hstar : e ∈ rStarSourceEdges m hm) (hr : e ∈ connectorReveal m hm A) :
    ∃ right : Bool, e ∈ sideOuterClusterReveal m right A := by
  have hr' : e ∈ slitScreenBallReveal m A ∨
      e ∈ sideOuterClusterReveal m false A ∨
      e ∈ sideOuterClusterReveal m true A ∨ e ∈ exteriorRevealEdges m hm := by
    simpa only [connectorReveal,connectorClusterReveal,sideJointReveal,jointReveal,
      Finset.mem_union,or_assoc] using hr
  rcases hr' with hball | hl | hr | hext
  · have hball' : ∀ v ∈ e.val, Thm4Side.slitScreenRadius m v ≤ (m:ℤ) := by
      simpa only [slitScreenBallReveal,slitScreenBallRevealEdges,Finset.mem_filter,
        Finset.mem_univ,true_and] using hball
    obtain ⟨⟨u,v⟩,heq⟩ := Sym2.mk_surjective e.val
    have hu : u ∈ e.val := heq ▸ Sym2.mem_mk_left u v
    have hc := rStarSourceEdges_endpoint_bounds m hm e hstar u hu
    have hb := hball' u hu
    change max |u.val.1| |u.val.2+(16*m:ℤ)| ≤ (m:ℤ) at hb
    have hh := (abs_le.mp ((le_max_right _ _).trans hb)).2
    omega
  · exact ⟨false,hl⟩
  · exact ⟨true,hr⟩
  · have hn : e ∉ rStarSourceEdges m hm := by
      simpa only [exteriorRevealEdges,Finset.mem_sdiff,Finset.mem_univ,true_and] using hext
    exact (hn hstar).elim

/-- A dual face off a full side screen and incident to a queried side bond
has the exterior index, retaining its original crossed-bond label. -/
theorem sideQuery_face_exteriorIndex (m : ℕ) (right : Bool)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
      (sideFaceBases m right)).Walk s t)
    (hsF : s ∈ sideFaceBases m right)
    (hs : s.2=-(16*(m:ℤ))-1) (ht : t.2=16*(m:ℤ))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (hr : e ∈ sideOuterClusterReveal m right A)
    (b : FKC.Medial.LatticeBond)
    (hb : FKC.Medial.latticeBondEdge b=FKC.FiniteFK.slitBoxEdgeEmbedding (16*m) e)
    (z : FKC.LatticeVertex) (hz : z ∈ (FKC.Medial.dualBondOfPrimal b).toSym2)
    (htrace : z ∉ p.support) (hrows : s.2 ≠ z.2 ∧ t.2 ≠ z.2) :
    rayIndex z (sourceScreenIndexWalk m A (sideFaceBases m right) p)=
      if right then 0 else 1 := by
  obtain ⟨u,hu,huc⟩ := (Thm3.Prop4.mem_censoredSeedReveal _ _ A e).mp hr
  have hidx := sideOuterCluster_sourceScreenIndex m right A p hsF hs ht u huc
  have hface : z ∈ (dualBondOfPrimal (latticeBondEquiv b)).toSym2 := by
    rw [← latticeBondEquiv_dualBondOfPrimal,latticeBondEquiv_toSym2]
    exact hz
  have hpoint : u.val ∈ (latticeBondEquiv b).toSym2 := by
    rw [latticeBondEquiv_toSym2]
    have hpair := congrArg Subtype.val hb
    change b.toSym2=Sym2.map Subtype.val e.val at hpair
    rw [hpair]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  have hc := screenIndex_crossedBond_endpoint
    (sourceScreenIndexWalk m A (sideFaceBases m right) p) (latticeBondEquiv b) z u.val
    (fun h => htrace ((sourceScreenIndexWalk_support m A _ p) ▸ h)) hrows.1 hrows.2 hface hpoint
  exact hc.symm.trans hidx

end
end PottsContinuity.Thm4Records
