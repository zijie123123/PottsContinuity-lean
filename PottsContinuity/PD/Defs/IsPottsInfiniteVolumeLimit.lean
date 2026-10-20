-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/IsPottsInfiniteVolumeLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.Box
public import PottsContinuity.PD.Defs.PottsProb
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# `IsPottsInfiniteVolumeLimit` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- `μ` is the infinite-volume Potts Gibbs measure `μⁱ_β`: the probability measure on
`{1,…,q}^{ℤ²}` to which `μⁱ_{Λₙ,β}` converge, tested on all finite-dimensional cylinder events.
The finite volumes are the boxes `Λₙ`; the Hamiltonian is the paper's literal
one, with one boundary term per vertex of `∂Λₙ`. -/
def IsPottsInfiniteVolumeLimit (q : ℕ) (β : ℝ) (i : Fin (q + 1))
    (μ : Measure (ℤ × ℤ → Set.Icc 1 q)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Set.Icc 1 q),
      Tendsto
        (fun n : ℕ =>
          ∑ σ : ↥(box n : Set (ℤ × ℤ)) → Set.Icc 1 q,
            if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x
            then pottsProb q (box n) β i σ else 0)
        atTop (𝓝 (μ.real {σ | ∀ x ∈ A, σ x = ξ x}))

end PottsContinuity.PD
