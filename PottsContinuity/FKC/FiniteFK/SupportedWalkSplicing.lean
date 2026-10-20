-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SupportedWalkSplicing.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open SimpleGraph

/-- Two vertices visited by a walk can be joined by retracing prefixes of that
same walk. The resulting walk uses no vertices outside the original support. -/
theorem walk_between_support {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v x y : V} (p : G.Walk u v) (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : G.Walk x y, q.support ⊆ p.support := by
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy), ?_⟩
  intro z hz
  rw [Walk.support_append] at hz
  rcases List.mem_append.mp hz with hz | hz
  · rw [Walk.support_reverse] at hz
    exact Walk.support_takeUntil_subset_support p hx (List.mem_reverse.mp hz)
  · exact Walk.support_takeUntil_subset_support p hy (List.mem_of_mem_tail hz)

end PottsContinuity.FKC.FiniteFK
