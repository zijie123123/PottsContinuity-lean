-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCWeight.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.RCFreeClusterCount
public import PottsContinuity.PD.Defs.RCWiredClusterCount
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# `rcWeight` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- The unnormalized weight `p^{o(ω)} (1-p)^{c(ω)} q^{kᵢ(ω)}`, `i ∈ {0, 1}`. -/
noncomputable def rcWeight (V : Finset (ℤ × ℤ)) (p q : ℝ) (i : Fin 2)
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  p ^ Nat.card {e // ω e = true} * (1 - p) ^ Nat.card {e // ω e = false} *
    q ^ (if i = 0 then rcFreeClusterCount V ω else rcWiredClusterCount V ω)

end PottsContinuity.PD
