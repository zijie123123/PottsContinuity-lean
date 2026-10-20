module

public import PottsContinuity.PlanarTopology.ArchRayIndex
public import PottsContinuity.PlanarTopology.KSTRectangleRealization
public import PottsContinuity.PD.Duality.WholePlaneDualConfiguration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.RCInfinite PD.Duality BD12
noncomputable section

/-- An actual open primal bond cannot occur among the crossing bonds of an
actual complementary dual walk, irrespective of its geometric shape. -/
theorem open_bond_dual_not_mem_walk (ω : LatticeConfiguration)
    {u v : LatticeVertex} (q : PD.squareLattice.Walk u v)
    (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (b : LatticeBond) (hb : latticeConfigurationBondState ω b = true) :
    (dualBondOfPrimal b).toSym2 ∉ q.edges := by
  intro he
  have hd := hq (latticeBondEdge (dualBondOfPrimal b)) he
  change latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω) (dualBondOfPrimal b) = true at hd
  rw [wholePlaneDualConfigurationHomeomorph_bondState,primalBondOfDual_dualBondOfPrimal,hb] at hd
  cases hd

/-- Closing the actual dual arch along the outside column preserves avoidance
for every original open bond of the right half-plane. The closing bonds need
no sampled state, since all their crossing primal bonds leave the half-plane. -/
theorem halfplane_open_edge_avoids_arch_closure (ω : LatticeConfiguration)
    {a b : LatticeVertex} (q : PD.squareLattice.Walk a b)
    (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (r : PD.squareLattice.Walk b a) (hr : ∀ z ∈ r.support, z.1 = -1)
    {u v : LatticeVertex} (hu : 0 ≤ u.1) (hv : 0 ≤ v.1)
    (huv : (PD.rcInfiniteOpenGraph ω).Adj u v) :
    (circuitAvoidanceGraph (q.append r)).Adj u v := by
  obtain ⟨hadj,hopen⟩ := (rcInfiniteOpenGraph_adj ω u v).mp huv
  refine ⟨PD.squareLattice.mem_edgeSet.mp hadj,?_⟩
  intro B hB he
  have hbopen : latticeConfigurationBondState ω B = true := by
    have heq : latticeBondEdge B = (⟨s(u,v),hadj⟩ : PD.squareLattice.edgeSet) := Subtype.ext hB
    change ω (latticeBondEdge B) = true
    rwa [heq]
  rw [SimpleGraph.Walk.edges_append,List.mem_append] at he
  rcases he with he | he
  · exact open_bond_dual_not_mem_walk ω q hq B hbopen he
  · have hcol := hr (dualBondOfPrimal B).target (r.snd_mem_support_of_mem_edges he)
    rw [dualBond_target_eq_source] at hcol
    have hmem : B.source ∈ s(u,v) := by
      rw [← hB]
      exact Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hmem with h | h
    · rw [h] at hcol
      omega
    · rw [h] at hcol
      omega

end
end PottsContinuity.PlanarTopology
