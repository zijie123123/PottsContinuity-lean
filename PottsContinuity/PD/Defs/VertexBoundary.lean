-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/VertexBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.SquareLattice
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# `vertexBoundary` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- `∂V`: the vertices of `V` having at least one neighbour in `ℤ²` outside of `V`. -/
def vertexBoundary (V : Finset (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {x | x ∈ V ∧ ∃ y, squareLattice.Adj x y ∧ y ∉ V}

end PottsContinuity.PD
