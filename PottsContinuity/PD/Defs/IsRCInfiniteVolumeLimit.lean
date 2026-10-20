-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/IsRCInfiniteVolumeLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.Box
public import PottsContinuity.PD.Defs.RCProb
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# `IsRCInfiniteVolumeLimit` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- `μ` is the infinite-volume random-cluster measure with boundary condition `i`: the
probability measure on `{0,1}^{E(ℤ²)}` to which `φⁱ_{Λₙ,p,q}` converge weakly, tested on all
finite-dimensional cylinder events. The finite volumes are the boxes `Λₙ`. -/
def IsRCInfiniteVolumeLimit (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset squareLattice.edgeSet) (ξ : squareLattice.edgeSet → Bool),
      Tendsto
        (fun n : ℕ =>
          ∑ ω : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet → Bool,
            if ∀ e ∈ A, ∃ f : (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet,
                Sym2.map Subtype.val f.1 = e.1 ∧ ω f = ξ e
            then rcProb (box n) p q i ω else 0)
        atTop (𝓝 (μ.real {ω | ∀ e ∈ A, ω e = ξ e}))

end PottsContinuity.PD
