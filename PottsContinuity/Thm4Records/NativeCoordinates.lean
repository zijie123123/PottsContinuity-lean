module

public import PottsContinuity.Thm4Records.NativeBoundaryOrder
public import PottsContinuity.Thm4Records.MaximalCompletion
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.NativeWindowCarrier

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

private theorem crossed_bond_endpoint_bounds (m : ℕ) (d : FKC.Medial.LatticeBond)
    (hs : d.source ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (ht : d.target ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (u : ℤ × ℤ) (hu : u ∈ (FKC.Medial.primalBondOfDual d).toSym2) :
    -(5*(m:ℤ)) ≤ u.1 ∧ u.1 ≤ 5*(m:ℤ) ∧
      -(12*(m:ℤ)) ≤ u.2 ∧ u.2 ≤ -(2*(m:ℤ)) := by
  rcases d with ⟨⟨x,y⟩,a⟩
  cases a <;>
    simp only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc,
      FKC.Medial.LatticeBond.source,FKC.Medial.LatticeBond.target,
      FKC.Medial.primalBondOfDual,FKC.Medial.LatticeBond.toSym2,
      ] at hs ht hu <;>
    rcases Sym2.mem_iff'.mp hu with rfl | rfl <;> dsimp <;> omega

/-- Every original bond crossed inside R* has its literal primal endpoints
in the surrounding primal square, with the full terminal rows retained. -/
theorem rStarSourceEdges_endpoint_bounds (m : ℕ) (hm : 1 ≤ m)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (he : e ∈ rStarSourceEdges m hm)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ e.val) :
    -(5*(m:ℤ)) ≤ u.val.1 ∧ u.val.1 ≤ 5*(m:ℤ) ∧
      -(12*(m:ℤ)) ≤ u.val.2 ∧ u.val.2 ≤ -(2*(m:ℤ)) := by
  classical
  obtain ⟨f,hf⟩ : ∃ f : (SlitRStarGraph m).edgeSet,
      (slitRStarEdgeBridge m hm f).primalEdge = e := by
    simpa only [rStarSourceEdges,Finset.mem_image,Finset.mem_univ,true_and] using he
  subst e
  let b := slitRStarEdgeBridge m hm f
  have hpair := congrArg Subtype.val b.crosses
  change (FKC.Medial.primalBondOfDual b.dualBond).toSym2 =
    Sym2.map Subtype.val b.primalEdge.val at hpair
  have hu' : u.val ∈ (FKC.Medial.primalBondOfDual b.dualBond).toSym2 := by
    rw [hpair]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  exact crossed_bond_endpoint_bounds m b.dualBond b.endpoints.1 b.endpoints.2 u.val hu'

/-- Every original bond touching either outer seed column is queried. -/
theorem source_edge_at_outer_column_queried (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ e.val)
    (hx : u.val.1 = -(5*(m:ℤ)) ∨ u.val.1 = 5*(m:ℤ)) :
    e ∈ connectorReveal m hm X := by
  have hseed (right : Bool) (hs : u ∈ sideOuterSeeds m right) :
      e ∈ connectorReveal m hm X := by
    apply sideOuterClusterReveal_subset_connectorReveal m hm right X
    exact (Thm3.Prop4.mem_censoredSeedReveal _ _ X e).mpr
      ⟨u,hu,u,hs,SimpleGraph.Reachable.refl _⟩
  rcases hx with hx | hx
  · exact hseed false hx
  · exact hseed true hx

/-- Incident native vertices lie strictly between the seed columns. Deleting
queried bonds preserves both primal terminal rows of R*. -/
theorem connectorNativeVertex_coordinates (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u : connectorNativeVertex m hm X) :
    -(5*(m:ℤ)) < u.val.val.1 ∧ u.val.val.1 < 5*(m:ℤ) ∧
      -(12*(m:ℤ)) ≤ u.val.val.2 ∧ u.val.val.2 ≤ -(2*(m:ℤ)) := by
  obtain ⟨v,hv⟩ := u.property
  obtain ⟨hG,hd⟩ := (PlanarMixed.edgeRestriction_adj_exists_not_mem _ _ u.val v).mp hv
  let e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet :=
    ⟨s(u.val,v),(FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr hG⟩
  have he : e ∉ connectorReveal m hm X := hd
  have hu : u.val ∈ e.val := Sym2.mem_mk_left _ _
  have hb := rStarSourceEdges_endpoint_bounds m hm e
    (remaining_edge_mem_rStarSourceEdges m hm X e he) u.val hu
  have hnot : ¬ (u.val.val.1 = -(5*(m:ℤ)) ∨ u.val.val.1 = 5*(m:ℤ)) :=
    fun hx => he (source_edge_at_outer_column_queried m hm X e u.val hu hx)
  exact ⟨by omega,by omega,hb.2.2⟩


/-- The original wired slit arc does not meet any native vertex of R*. -/
theorem connectorNativeVertex_not_slitBoundary (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u : connectorNativeVertex m hm X) :
    u.val ∉ (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m))).boundary := by
  have hc := connectorNativeVertex_coordinates m hm X u
  intro h
  change u.val ∈ FKC.FiniteFK.slitBoxWiredArc (16*m) at h
  have hy := ((FKC.FiniteFK.mem_slitBoxWiredArc_iff _ _).mp h).2.1
  omega

private theorem crossed_bond_not_terminal_row (m : ℕ) (d : FKC.Medial.LatticeBond)
    (hs : d.source ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (ht : d.target ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m)
    (u v : ℤ × ℤ) (huv : (FKC.Medial.primalBondOfDual d).toSym2 = s(u,v)) :
    ¬ (u.2 = -(12*(m:ℤ)) ∧ v.2 = -(12*(m:ℤ))) ∧
      ¬ (u.2 = -(2*(m:ℤ)) ∧ v.2 = -(2*(m:ℤ))) := by
  rcases d with ⟨⟨x,y⟩,a⟩
  cases a <;>
    simp only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc,
      FKC.Medial.LatticeBond.source,FKC.Medial.LatticeBond.target,
      FKC.Medial.primalBondOfDual,FKC.Medial.LatticeBond.toSym2] at hs ht huv <;>
    rcases Sym2.eq_iff.mp huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> dsimp <;> omega

/-- The square's top and bottom primal side bonds are not among its crossed
original bonds. They therefore cannot reappear on the residual carrier. -/
theorem rStarSourceEdges_not_terminal_row (m : ℕ) (hm : 1 ≤ m)
    (u v : FKC.FiniteFK.SlitBoxVertex (16*m))
    (huv : (FKC.FiniteFK.slitBoxGraph (16*m)).Adj u v)
    (he : (⟨s(u,v),(FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr huv⟩ :
      (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet) ∈ rStarSourceEdges m hm) :
    ¬ (u.val.2 = -(12*(m:ℤ)) ∧ v.val.2 = -(12*(m:ℤ))) ∧
      ¬ (u.val.2 = -(2*(m:ℤ)) ∧ v.val.2 = -(2*(m:ℤ))) := by
  classical
  obtain ⟨f,hf⟩ : ∃ f : (SlitRStarGraph m).edgeSet,
      (slitRStarEdgeBridge m hm f).primalEdge =
        ⟨s(u,v),(FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr huv⟩ := by
    simpa only [rStarSourceEdges,Finset.mem_image,Finset.mem_univ,true_and] using he
  let b := slitRStarEdgeBridge m hm f
  have hp := congrArg Subtype.val b.crosses
  change (FKC.Medial.primalBondOfDual b.dualBond).toSym2 =
    Sym2.map Subtype.val b.primalEdge.val at hp
  rw [hf] at hp
  exact crossed_bond_not_terminal_row m b.dualBond b.endpoints.1 b.endpoints.2 u.val v.val hp

end
end PottsContinuity.Thm4Records
