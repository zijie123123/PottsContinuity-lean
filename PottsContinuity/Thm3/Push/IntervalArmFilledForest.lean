module

public import PottsContinuity.Thm3.Push.IntervalArmFilledNoCycles
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PlanarTopology
noncomputable section

/-- The filled source frontier is a forest on the ORIGINAL primal vertices.
No source crossing or interval nondegeneracy is required for this statement. -/
theorem intervalArmFilledLeftFrontier_isAcyclic (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    (openGraph (rectangleGraph (0,0) N N) (intervalArmFilledLeftFrontier N l r A)).IsAcyclic := by
  intro v q hq
  let F := intervalArmFilledLeftFrontier N l r A
  let j := rectangleOpenGraphToSquare (0,0) N N F
  let p := q.map j
  have hp : p.IsCycle := hq.map (by
    intro x y hxy
    exact Subtype.ext hxy)
  have hinside : ∀ x ∈ p.support, x ∈ latticeRectangle (0,0) N N := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    exact u.property
  have htrace := rectangle_open_walk_trace_subset (0,0) N N F q
  have hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A := by
    intro f hf
    apply htrace
    apply (mem_rectangleTraceConfiguration (0,0) N N p f).mpr
    erw [rectanglePrimalEdgeBond_toSym2_public] at hf
    exact hf
  have hzero := interval_filled_frontier_closed_trail_length_zero N l r A p
    hp.isTrail.edges_nodup hinside hedges
  exact hp.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp hzero)

end
end PottsContinuity.Push
