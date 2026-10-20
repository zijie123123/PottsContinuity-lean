module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Thm1.Uniqueness

/-!
# Proof of `PottsContinuity.isPottsInfiniteVolumeLimit_unique`

This module proves `PottsContinuity.Provider.isPottsInfiniteVolumeLimit_unique`, whose statement is
exactly that of `isPottsInfiniteVolumeLimit_unique` in
`Frozen/IsPottsInfiniteVolumeLimitUnique.lean` (with implicit binders and auto-param hypotheses), by
`Thm1.potts_limit_unique`. The proof in `Frozen/IsPottsInfiniteVolumeLimitUnique.lean` is `by exact`
this theorem; no other module imports this one.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.isPottsInfiniteVolumeLimit_unique`, with implicit
binders and auto-param hypotheses, so that its proof in
`Frozen/IsPottsInfiniteVolumeLimitUnique.lean` is `by exact` this theorem. -/
theorem isPottsInfiniteVolumeLimit_unique {q : ℕ} {β : ℝ} {i : Fin q}
    {μ ν : Measure (ℤ × ℤ → Fin q)}
    (hμ : IsPottsInfiniteVolumeLimit q β i μ := by assumption)
    (hν : IsPottsInfiniteVolumeLimit q β i ν := by assumption) : μ = ν :=
  Thm1.potts_limit_unique q β i μ ν hμ hν

end PottsContinuity.Provider
