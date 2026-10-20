-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCOpenGraph.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.SquareLattice
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# `rcOpenGraph` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- The open subgraph of a percolation configuration `ω ∈ {0,1}^E` on the finite subgraph
`G = (V, E)` of `ℤ²` induced by `V` (vertex set `V`, open edges `{e ∈ E : ω(e) = 1}`). -/
def rcOpenGraph (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :
    SimpleGraph (V : Set (ℤ × ℤ)) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ h : e ∈ (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet, ω ⟨e, h⟩ = true}

end PottsContinuity.PD
