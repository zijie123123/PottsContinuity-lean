-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/SquareLattice.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# `squareLattice` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- The square lattice `ℤ²`: vertices `x = (x₁, x₂)`, edges between nearest neighbours. -/
def squareLattice : SimpleGraph (ℤ × ℤ) where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by rwa [abs_sub_comm y.1, abs_sub_comm y.2]⟩
  loopless := ⟨fun x h => by simp at h⟩

end PottsContinuity.PD
