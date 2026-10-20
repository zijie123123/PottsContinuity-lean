-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateArcNeighbors.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateBaseEdges
public import PottsContinuity.FKC.FiniteFK.SlitBoxCanonicalReturnEdges
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open SimpleGraph

private theorem cycleNeighborSet_eq_walkEdges
    {z : LatticeVertex} (c : squareLattice.Walk z z) (x : LatticeVertex) :
    c.toSubgraph.spanningCoe.neighborSet x = {y | s(x,y) ∈ c.edges} := by
  ext y
  change c.toSubgraph.Adj x y ↔ s(x,y) ∈ c.edges
  rw [← SimpleGraph.Subgraph.mem_edgeSet]
  exact SimpleGraph.Walk.mem_edges_toSubgraph c

end PottsContinuity.FKC.FiniteFK
