module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

/-- A primal walk whose used bonds avoid the bonds crossed by a closed dual
walk has constant dual ray index at its endpoints. -/
theorem primalWalk_rayIndex_eq_of_crossedEdges_avoided
    {z u v : LatticeVertex} (p : squareLattice.Walk z z)
    (q : squareLattice.Walk u v)
    (havoid : ∀ e ∈ q.edges, ∀ b : LatticeBond, b.toSym2 = e →
      (dualBondOfPrimal b).toSym2 ∉ p.edges) :
    rayIndex u p = rayIndex v p := by
  have hreach : (circuitAvoidanceGraph p).Reachable u v := by
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b v hab tail ih =>
      have hhead : s(a, b) ∈ (SimpleGraph.Walk.cons hab tail).edges := by
        simp
      have hstep : (circuitAvoidanceGraph p).Adj a b := by
        refine ⟨hab, ?_⟩
        intro e he hcross
        exact havoid (s(a, b)) hhead e he hcross
      have htail : ∀ e ∈ tail.edges, ∀ b : LatticeBond,
          b.toSym2 = e → (dualBondOfPrimal b).toSym2 ∉ p.edges := by
        intro e he b hb hcross
        apply havoid e ?_ b hb hcross
        simp [he]
      exact hstep.reachable.trans (ih htail)
  exact rayIndex_eq_of_avoidance_reachable p hreach

/-- Different endpoint indices rule out every primal walk whose used bonds
avoid the bonds crossed by the closed dual walk. -/
theorem no_primalWalk_of_distinct_rayIndex_and_crossedEdges_avoided
    {z u v : LatticeVertex} (p : squareLattice.Walk z z)
    (q : squareLattice.Walk u v)
    (hu : rayIndex u p ≠ 0) (hv : rayIndex v p = 0)
    (havoid : ∀ e ∈ q.edges, ∀ b : LatticeBond, b.toSym2 = e →
      (dualBondOfPrimal b).toSym2 ∉ p.edges) : False := by
  have hindex := primalWalk_rayIndex_eq_of_crossedEdges_avoided p q havoid
  rw [hv] at hindex
  exact hu hindex

end PottsContinuity.DualityExt
