-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/IsTranslationErgodic.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Map

/-!
# `IsTranslationErgodic` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

/-- `μ` is invariant under every translation of `ℤ²`, and every measurable event invariant under
all translations of `ℤ²` is null or conull (ergodicity with respect to the translations of `ℤ²`). -/
def IsTranslationErgodic {S : Type*} [MeasurableSpace S] (μ : Measure (ℤ × ℤ → S)) : Prop :=
  (∀ a : ℤ × ℤ, μ.map (fun σ x => σ (x + a)) = μ) ∧
    ∀ s : Set (ℤ × ℤ → S), MeasurableSet s →
      (∀ a : ℤ × ℤ, (fun σ x => σ (x + a)) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0

end PottsContinuity.PD
