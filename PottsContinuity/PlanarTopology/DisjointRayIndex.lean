module

public import PottsContinuity.PD.Duality.RayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Disjoint lattice supports avoid the dual interpretation of a lattice loop.
The dual bond crossing a primal bond has the primal source among its endpoints.
Thus this implication does not require a continuous embedding argument.
-/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

/-- The upper/right endpoint of the crossing dual bond is the primal source,
when both lattices are recorded by their integer base coordinates. -/
theorem dualBond_target_eq_source (b : LatticeBond) :
    (dualBondOfPrimal b).target = b.source := by
  rcases b with ⟨⟨x, y⟩, ax⟩
  cases ax <;> simp [dualBondOfPrimal, LatticeBond.source, LatticeBond.target]

/-- A lattice walk disjoint from a closed lattice walk has the same ray index
at both endpoints, with the closed walk interpreted as dual face bases. -/
theorem rayIndex_eq_of_disjoint_support {z u v : LatticeVertex}
    (p : squareLattice.Walk z z) (q : squareLattice.Walk u v)
    (hdis : ∀ x ∈ q.support, x ∉ p.support) :
    rayIndex u p = rayIndex v p := by
  apply rayIndex_eq_of_avoidance_reachable p
  have hmap : ∀ {a b : LatticeVertex}, s(a,b) ∈ q.edges →
      (circuitAvoidanceGraph p).Adj a b := by
    intro a b hab
    refine ⟨q.adj_of_mem_edges hab, ?_⟩
    intro e he hcross
    have hsource : e.source ∈ q.support := by
      have hmem : e.source ∈ s(a,b) := by
        rw [← he]
        exact Sym2.mem_mk_left _ _
      rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
      · exact q.fst_mem_support_of_mem_edges hab
      · exact q.snd_mem_support_of_mem_edges hab
    have hdual : (dualBondOfPrimal e).target ∈ p.support :=
      p.snd_mem_support_of_mem_edges hcross
    rw [dualBond_target_eq_source] at hdual
    exact hdis e.source hsource hdual
  have hreach : (circuitAvoidanceGraph p).Reachable u v := by
    clear hdis
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b v hab q ih =>
      have hed : s(a,b) ∈ (q.cons hab).edges := by simp
      have hfirst := hmap hed
      have htail : ∀ {a b : LatticeVertex}, s(a,b) ∈ q.edges →
          (circuitAvoidanceGraph p).Adj a b := by
        intro a b he
        apply hmap
        simp [he]
      exact hfirst.reachable.trans (ih htail)
  exact hreach

end PottsContinuity.PlanarTopology
