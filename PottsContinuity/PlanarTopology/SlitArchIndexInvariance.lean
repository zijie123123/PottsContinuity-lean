module

public import PottsContinuity.PlanarTopology.SlitArchSampledGeometry
public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.FiniteFK FKC.Medial Thm4Plane
noncomputable section

local instance slitArchIndexEdgeFintype (m : ℕ) :
    Fintype (slitBoxGraph (16*m)).edgeSet := Fintype.ofFinite _

/-- Dual normalization commutes with the faithful bond translation. -/
theorem pdBondOfFKC_dual_toSym2 (b : LatticeBond) :
    (pdBondOfFKC (dualBondOfPrimal b)).toSym2 =
      (PD.FK.Medial.dualBondOfPrimal (pdBondOfFKC b)).toSym2 := by
  rcases b with ⟨base,axis⟩
  cases axis <;> rfl

/-- An edge remaining after deletion of the arch's crossed original bonds
preserves the arch index, provided it lies above the two arch endpoints. -/
theorem slit_arch_index_eq_of_residual_adj (m : ℕ)
    (A : Configuration (slitBoxGraph (16*m))) {s t : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16*m) A
      (generalScreenArchFaceBases (16*m))).Walk s t)
    {u v : SlitBoxVertex (16*m)}
    (hadj : (edgeRestriction (slitBoxGraph (16*m))
      (screenArchCrossedBondConfiguration m A p)).Adj u v)
    (hs : s.2 < min u.val.2 v.val.2) (ht : t.2 < min u.val.2 v.val.2) :
    PD.Duality.rayIndex u.val (p.map (slitScreenDualToIndexLattice _ _ _)) =
      PD.Duality.rayIndex v.val (p.map (slitScreenDualToIndexLattice _ _ _)) := by
  classical
  have hbase := edgeRestriction_le (slitBoxGraph (16*m))
    (screenArchCrossedBondConfiguration m A p) hadj
  have hlat := ((slitBoxGraph_adj_iff (16*m) u v).mp hbase).1
  apply open_arch_rayIndex_eq_of_avoiding_adj _
    ((PD.FK.squareLattice_adj_iff _ _).mpr ((FKC.squareLattice_adj_iff _ _).mp hlat)) hs ht
  intro b hb hcross
  obtain ⟨c,hc⟩ := LatticeBond.exists_of_adj hlat
  have hbc : pdBondOfFKC c = b :=
    PD.FK.Medial.LatticeBond.toSym2_injective ((pdBondOfFKC_toSym2 c).trans (hc.trans hb.symm))
  have hcross' : (dualBondOfPrimal c).toSym2 ∈ p.edges := by
    rw [← hbc,← pdBondOfFKC_dual_toSym2,pdBondOfFKC_toSym2] at hcross
    have hedges := slitScreenDualToIndexLattice_walk_edges (16*m) A
      (generalScreenArchFaceBases (16*m)) p
    exact hedges ▸ hcross
  let e : (slitBoxGraph (16*m)).edgeSet :=
    ⟨s(u,v),(slitBoxGraph (16*m)).mem_edgeSet.mpr hbase⟩
  have heR : e ∈ screenArchCrossedBondConfiguration m A p := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,dualBondOfPrimal c,?_,hcross'⟩
    rw [primalBondOfDual_dualBondOfPrimal]
    apply Subtype.ext
    exact hc
  have hnot := (SimpleGraph.deleteEdges_adj.mp hadj).2
  exact hnot ((coe_mem_openEdges_iff (slitBoxGraph (16*m))
    (screenArchCrossedBondConfiguration m A p) e).mpr heR)

/-- The arch index is unchanged throughout every component above its endpoints
in the graph obtained by deleting exactly its crossed sampled bonds. -/
theorem slit_arch_index_eq_of_residual_walk (m : ℕ)
    (A : Configuration (slitBoxGraph (16*m))) {s t : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16*m) A
      (generalScreenArchFaceBases (16*m))).Walk s t)
    {u v : SlitBoxVertex (16*m)}
    (q : (edgeRestriction (slitBoxGraph (16*m))
      (screenArchCrossedBondConfiguration m A p)).Walk u v)
    (hheight : ∀ z ∈ q.support, s.2 < z.val.2 ∧ t.2 < z.val.2) :
    PD.Duality.rayIndex u.val (p.map (slitScreenDualToIndexLattice _ _ _)) =
      PD.Duality.rayIndex v.val (p.map (slitScreenDualToIndexLattice _ _ _)) := by
  induction q with
  | nil => rfl
  | @cons u z v hadj q ih =>
    have hu := hheight u (by simp)
    have hz := hheight z (by simp)
    exact (slit_arch_index_eq_of_residual_adj m A p hadj (by omega) (by omega)).trans
      (ih (fun w hw => hheight w (by simp [hw])))

end
end PottsContinuity.PlanarTopology
