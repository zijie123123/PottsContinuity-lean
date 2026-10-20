module

public import PottsContinuity.Thm3.RSW.FiniteDualScreen
public import PottsContinuity.PD.RCInfinite.SubgraphProbability
public import PottsContinuity.PD.Duality.CircuitEnclosure

/-! # Exact sampled closed-dual states under finite closed extension -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

/-- Closing unsampled bonds gives exactly the finite sampled closure predicate
on every dual-walk edge, including edges outside the finite domain. -/
theorem finiteDualWalkClosed_iff_closedExtension_bondStates
    (V : Finset LatticeVertex)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z) :
    finiteDualWalkClosed V A p ↔
      ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ p.edges →
        latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A) b = false := by
  classical
  constructor
  · intro h b hb
    change decide (latticeBondEdge b ∈ A.map (frozenEdgeEmbedding V)) = false
    rw [decide_eq_false_iff_not]
    intro hm
    obtain ⟨e,he,heb⟩ := Finset.mem_map.mp hm
    apply h b hb e _ he
    exact congrArg Subtype.val heb
  · intro h b hb e heb he
    have hc := h b hb
    have hm : latticeBondEdge b ∈ A.map (frozenEdgeEmbedding V) := by
      apply Finset.mem_map.mpr
      exact ⟨e,he,Subtype.ext heb⟩
    have ho : latticeConfigurationBondState (finiteSubgraphConfiguration V 0 A) b = true := by
      change decide (latticeBondEdge b ∈ A.map (frozenEdgeEmbedding V)) = true
      exact decide_eq_true hm
    rw [hc] at ho
    cases ho

/-- The finite sampled closure predicate is exactly the assertion that all
walk edges are edges of the actual closed-dual graph of the closed extension. -/
theorem finiteDualWalkClosed_iff_closedExtension_dualAdj
    (V : Finset LatticeVertex)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    {z : LatticeVertex} (p : PD.FK.squareLattice.Walk z z) :
    finiteDualWalkClosed V A p ↔
      ∀ u v : LatticeVertex, s(u,v) ∈ p.edges →
        (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).Adj u v := by
  rw [finiteDualWalkClosed_iff_closedExtension_bondStates]
  constructor
  · intro h u v he
    obtain ⟨d,hd⟩ := LatticeBond.exists_of_adj (p.adj_of_mem_edges he)
    apply (wholePlaneClosedDualGraph_adj_iff_dualBond _ u v).mpr
    refine ⟨d,?_,?_⟩
    · apply h (primalBondOfDual d)
      simpa only [dualBondOfPrimal_primalBondOfDual,hd] using he
    · exact Sym2.eq_iff.mp hd.symm
  · intro h b hb
    have hs := closedDual_bond_state (finiteSubgraphConfiguration V 0 A)
      (dualBondOfPrimal b) (h _ _ hb)
    simpa only [primalBondOfDual_dualBondOfPrimal] using hs

end PottsContinuity.RSW
