-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCWiredClusterCount.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.RCOpenGraph
public import PottsContinuity.PD.Defs.VertexBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# `rcWiredClusterCount` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- `k₁(ω)`: the number of clusters when all clusters intersecting `∂V` count as one. -/
noncomputable def rcWiredClusterCount (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℕ :=
  Nat.card {c : (rcOpenGraph V ω).ConnectedComponent //
      ∀ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c →
        x.1 ∉ vertexBoundary V} +
    if ∃ c : (rcOpenGraph V ω).ConnectedComponent,
        ∃ x : (V : Set (ℤ × ℤ)), (rcOpenGraph V ω).connectedComponentMk x = c ∧
          x.1 ∈ vertexBoundary V then 1 else 0

end PottsContinuity.PD
