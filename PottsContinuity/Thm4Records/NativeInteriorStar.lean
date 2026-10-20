module

public import PottsContinuity.Thm4Records.NativeCoordinates

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- The full original star at an interior primal square vertex is crossed by
R*. No queried edge is restored by this geometric statement. -/
theorem source_edge_interior_mem_rStarSourceEdges (m : ℕ) (hm : 1 ≤ m)
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet)
    (u : FKC.FiniteFK.SlitBoxVertex (16*m)) (hu : u ∈ e.val)
    (hx : -(5*(m:ℤ)) < u.val.1 ∧ u.val.1 < 5*(m:ℤ))
    (hy : -(12*(m:ℤ)) < u.val.2 ∧ u.val.2 < -(2*(m:ℤ))) :
    e ∈ rStarSourceEdges m hm := by
  classical
  let b := FKC.Medial.wholePlaneBondEdgeEquiv.symm (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m) e)
  let d := FKC.Medial.dualBondOfPrimal b
  have hp : b.toSym2 = Sym2.map Subtype.val e.val :=
    congrArg Subtype.val (Equiv.apply_symm_apply FKC.Medial.wholePlaneBondEdgeEquiv
      (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m) e))
  have hub : u.val ∈ b.toSym2 := by
    rw [hp]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  have hds : -(5*(m:ℤ)) ≤ d.source.1 ∧ d.source.1 ≤ 5*(m:ℤ)-1 ∧
      -(12*(m:ℤ)) ≤ d.source.2 ∧ d.source.2 ≤ -(2*(m:ℤ))-1 := by
    dsimp [d]
    rcases b with ⟨⟨x,y⟩,a⟩
    cases a <;> dsimp [FKC.Medial.dualBondOfPrimal,FKC.Medial.LatticeBond.source,
      FKC.Medial.LatticeBond.toSym2,FKC.Medial.LatticeBond.target] at hub ⊢ <;>
      rcases Sym2.mem_iff'.mp hub with h | h <;> rw [h] at hx hy <;>
      dsimp at hx hy <;> omega
  have hdt : -(5*(m:ℤ)) ≤ d.target.1 ∧ d.target.1 ≤ 5*(m:ℤ)-1 ∧
      -(12*(m:ℤ)) ≤ d.target.2 ∧ d.target.2 ≤ -(2*(m:ℤ))-1 := by
    dsimp [d]
    rcases b with ⟨⟨x,y⟩,a⟩
    cases a <;> dsimp [FKC.Medial.dualBondOfPrimal,FKC.Medial.LatticeBond.source,
      FKC.Medial.LatticeBond.toSym2,FKC.Medial.LatticeBond.target] at hub ⊢ <;>
      rcases Sym2.mem_iff'.mp hub with h | h <;> rw [h] at hx hy <;>
      dsimp at hx hy <;> omega
  have hmem (z : ℤ × ℤ)
      (hz : -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
        -(12*(m:ℤ)) ≤ z.2 ∧ z.2 ≤ -(2*(m:ℤ))-1) :
      z ∈ PD.FK.latticeRectangle (slitScreenRStarBase m)
        (slitScreenRStarSide m) (slitScreenRStarSide m) := by
    rw [PD.FK.mem_latticeRectangle]
    dsimp [slitScreenRStarBase,slitScreenRStarSide]
    constructor <;> constructor <;> omega
  let s : SlitRStarVertex m := ⟨d.source,hmem _ hds⟩
  let t : SlitRStarVertex m := ⟨d.target,hmem _ hdt⟩
  have hadj : (SlitRStarGraph m).Adj s t := by
    apply (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr
    apply (PD.FK.squareLattice_adj_iff _ _).mpr
    exact (FKC.squareLattice_adj_iff _ _).mp d.adjacent
  let f : (SlitRStarGraph m).edgeSet := ⟨s(s,t),(SlitRStarGraph m).mem_edgeSet.mpr hadj⟩
  have hd : (slitRStarEdgeBridge m hm f).dualBond = d := by
    apply FKC.Medial.LatticeBond.toSym2_injective
    exact (slitRStarEdgeBridge m hm f).pairEq
  have he : (slitRStarEdgeBridge m hm f).primalEdge = e := by
    apply (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m)).injective
    rw [← (slitRStarEdgeBridge m hm f).crosses,hd]
    change FKC.Medial.latticeBondEdge (FKC.Medial.primalBondOfDual
      (FKC.Medial.dualBondOfPrimal b)) = _
    rw [FKC.Medial.primalBondOfDual_dualBondOfPrimal]
    exact Equiv.apply_symm_apply FKC.Medial.wholePlaneBondEdgeEquiv _
  simp only [rStarSourceEdges,Finset.mem_image,Finset.mem_univ,true_and]
  exact ⟨f,he⟩

end
end PottsContinuity.Thm4Records
