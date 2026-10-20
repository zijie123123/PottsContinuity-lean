-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/RCProb.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.RCWeight
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# `rcProb` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- The finite-volume random-cluster measure `φⁱ_{G,p,q}(ω) = weight / Zⁱ(G,p,q)`, for the
source parameter range `p ∈ [0, 1]`, `q > 0`. -/
noncomputable def rcProb (V : Finset (ℤ × ℤ)) (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (i : Fin 2) (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : ℝ :=
  rcWeight V p q i ω / ∑ ω', rcWeight V p q i ω'

end PottsContinuity.PD
