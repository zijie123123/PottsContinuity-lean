module

public import PottsContinuity.PlanarMixed.FiniteSlit.InducedDualLaw

/-! Exact forced-open dual states in the balanced rectangle. The only OPEN
exterior dual bonds cross the deleted horizontal slit bonds above the tip. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitForcedDualStateEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Literal normalized edge on the host graph carrier. -/
def originalBondEdge (M : ℕ) (x : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet :=
  ⟨s(⟨b.source,hs⟩,⟨b.target,ht⟩),(rectangleGraph _ _ _).mem_edgeSet.mpr b.adjacent⟩

/-- The rectangular auxiliary state is precisely internal alpha/beta bonds. -/
theorem rectangleArcBonds_mem_bond_iff (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    originalBondEdge M x b hs ht ∈
      rectangleArcBonds M x y ↔ boundaryInternal M x y b := by
  have hG : (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).Adj
      ⟨b.source,hs⟩ ⟨b.target,ht⟩ := b.adjacent
  dsimp only [originalBondEdge]
  rw [rectangleArcBonds,Finset.mem_union,mem_internalBonds_pair _ _ _ _ hG,
    mem_internalBonds_pair _ _ _ _ hG]
  constructor
  · exact fun h => ⟨hs,ht,h⟩
  · rintro ⟨_,_,h⟩
    exact h

/-- A normalized original edge belongs to the actual active sampled graph
exactly when its full active-bond predicate holds. -/
theorem rectangleBond_mem_active_iff (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    (originalBondEdge M x b hs ht).val ∈
      (activeGraph M x y).edgeSet ↔ ActiveBond M x y b :=
  activeGraph_bond_adj_iff M x y b hs ht

/-- Complementing the fixed exterior state opens exactly nonretained bonds
that were not auxiliary arc bonds. This statement is on the actual dual host. -/
theorem dualExteriorState_mem_crossing_iff (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
      (originalBondEdge M x b hs ht) ∈
        (dualExteriorState M x y).val ↔
      ¬ boundaryInternal M x y b ∧ ¬ SlitRetainedBond x y b := by
  change _ ∈ positiveRectangleDualConfigurationEquiv _ _ _ _ ∩ dualRemovedEdges M x y ↔ _
  rw [Finset.mem_inter,rectangleDualEdgeEquiv_mem_dualConfiguration]
  simp only [exteriorState,dualRemovedEdges,rectangleSubgraphRemovedDualEdges,
    Finset.mem_map_equiv,Equiv.symm_apply_apply,mem_subgraphRemovedEdges]
  rw [rectangleArcBonds_mem_bond_iff,rectangleBond_mem_active_iff]
  simp only [ActiveBond,hs,ht,true_and]
  tauto

/-- In the genuine finite regime the forced state is precisely the deleted
slit, with the STRICT original height inequality. -/
theorem dualExteriorState_mem_crossing_iff_slit (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (_hyM : y < (M : ℤ)) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
      (originalBondEdge M x b hs ht) ∈
        (dualExteriorState M x y).val ↔
      b.axis = .horizontal ∧ b.base.1 = x-1 ∧ y < b.base.2 := by
  rw [dualExteriorState_mem_crossing_iff M x y b hs ht]
  have hi : boundaryInternal M x y b ↔
      ((⟨b.source,hs⟩ : Vertex M x) ∈ alpha M x ∧ ⟨b.target,ht⟩ ∈ alpha M x) ∨
      ((⟨b.source,hs⟩ : Vertex M x) ∈ beta M x y ∧ ⟨b.target,ht⟩ ∈ beta M x y) := by
    constructor
    · rintro ⟨_,_,h⟩; exact h
    · exact fun h => ⟨hs,ht,h⟩
  rw [hi]
  have hsb := (mem_rectangle_iff M x (by omega) b.source).mp hs
  have htb := (mem_rectangle_iff M x (by omega) b.target).mp ht
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax <;> simp [alpha,beta,SlitRetainedBond,LatticeBond.source,LatticeBond.target,
    ] at * <;> omega

/-- Every normalized rectangle edge's crossing has its actual geometric bond. -/
theorem crossingEdge_global (M : ℕ) (x : ℤ) (b : LatticeBond) (hs ht) :
    rectangleDualEdgeToSquareEdge (x-(M : ℤ),0) (2*M-1) M
      (rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M
        (originalBondEdge M x b hs ht)) =
      latticeBondEdge (dualBondOfPrimal b) := by
  change rectangleDualEdgeToSquareEdge _ _ _
    (rectangleDualGraphEdgeEquiv _ _ _ (crossingEdge M x b hs ht)) = _
  rw [rectangleDualEdgeToSquareEdge_carrier,crossingEdge_bond]

end
end PottsContinuity.PlanarMixed.FiniteSlit
