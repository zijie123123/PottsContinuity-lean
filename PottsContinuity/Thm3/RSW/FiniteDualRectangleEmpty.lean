module

public import PottsContinuity.Thm3.RSW.Lemma4BandProduct
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import PottsContinuity.PlanarTopology.HorizontalWalks

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- Closing every original sampled bond leaves every square-lattice dual
step open, including all unsampled bonds under the closed extension. -/
theorem squareLattice_le_finite_closedDual_empty (V : Finset LatticeVertex) :
    PD.FK.squareLattice ≤ wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 ∅) := by
  intro u v huv
  obtain ⟨d,hd⟩ := wholePlaneBondEdgeEquiv.surjective ⟨s(u,v),PD.FK.squareLattice.mem_edgeSet.mpr huv⟩
  apply (wholePlaneClosedDualGraph_adj_iff_dualBond _ _ _).mpr
  refine ⟨d,?_,?_⟩
  · simp only [latticeConfigurationBondState,finiteSubgraphConfiguration,dite_true,
      Finset.map_empty,Finset.notMem_empty,decide_false]
  · have heq : s(u,v) = s(d.source,d.target) := (congrArg Subtype.val hd).symm
    exact Sym2.eq_iff.mp heq

/-- Every nonempty closed integer rectangle has a literal horizontal dual
crossing when all original sampled bonds are closed. -/
theorem empty_mem_finiteClosedDualHorizontalRectangle
    (V : Finset LatticeVertex) (l r b t : ℤ) (hlr : l ≤ r) (hbt : b ≤ t) :
    (∅ : Configuration (finiteLatticeGraph V)) ∈ finiteClosedDualHorizontalRectangle V l r b t := by
  obtain ⟨p,hp⟩ := PlanarTopology.horizontal_walk_between l r b
  refine ⟨(l,b),(r,b),p.mapLe (squareLattice_le_finite_closedDual_empty V),rfl,rfl,?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  have h := hp x hx
  rw [min_eq_left hlr,max_eq_right hlr] at h
  exact ⟨h.1,h.2.1,by omega,by omega⟩

end
end PottsContinuity.RSW
