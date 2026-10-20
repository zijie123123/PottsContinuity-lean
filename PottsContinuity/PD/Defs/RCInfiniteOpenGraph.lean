-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCInfiniteOpenGraph.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.SquareLattice
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# `rcInfiniteOpenGraph` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- The open subgraph of `ℤ²` of an infinite-volume configuration `ω ∈ {0,1}^{E(ℤ²)}`. -/
def rcInfiniteOpenGraph (ω : squareLattice.edgeSet → Bool) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ squareLattice.edgeSet, ω ⟨e, h⟩ = true}

end PottsContinuity.PD
