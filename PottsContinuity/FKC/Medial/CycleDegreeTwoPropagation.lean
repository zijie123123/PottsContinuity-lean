-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/CycleDegreeTwoPropagation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- At a vertex on a simple cycle, any ambient degree-two graph containing the
cycle has exactly the cycle's two neighbors. -/
theorem cycle_neighborSet_eq_of_degree_two
    {V : Type*} {G₀ G : SimpleGraph V} {u : V}
    (c : G₀.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe ≤ G)
    {x : V} (hx : x ∈ c.support)
    (hdeg : (G.neighborSet x).ncard = 2) :
    G.neighborSet x = c.toSubgraph.spanningCoe.neighborSet x := by
  classical
  let C := c.toSubgraph.spanningCoe
  have hsub : C.neighborSet x ⊆ G.neighborSet x :=
    SimpleGraph.neighborSet_mono hspan x
  have hCcard : (C.neighborSet x).ncard = 2 := by
    change (c.toSubgraph.neighborSet x).ncard = 2
    exact hc.ncard_neighborSet_toSubgraph_eq_two hx
  have hGpos : 0 < (G.neighborSet x).ncard := by rw [hdeg]; omega
  have hGfinite : (G.neighborSet x).Finite := Set.finite_of_ncard_pos hGpos
  apply (Set.eq_of_subset_of_ncard_le hsub ?_ hGfinite).symm
  rw [hCcard, hdeg]

end PottsContinuity.FKC.Medial
