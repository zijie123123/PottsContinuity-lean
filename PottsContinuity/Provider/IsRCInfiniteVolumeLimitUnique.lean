module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.WellDefined.Uniqueness

/-!
# Proof of `PottsContinuity.isRCInfiniteVolumeLimit_unique`

This module proves `PottsContinuity.Provider.isRCInfiniteVolumeLimit_unique`, whose statement is
exactly that of `isRCInfiniteVolumeLimit_unique` in `Frozen/IsRCInfiniteVolumeLimitUnique.lean`
(with implicit binders and auto-param hypotheses), by `WellDefined.limit_unique`. The proof in
`Frozen/IsRCInfiniteVolumeLimitUnique.lean` is `by exact` this theorem; no other module imports this
one.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.isRCInfiniteVolumeLimit_unique`, with implicit binders
and auto-param hypotheses, so that its proof in `Frozen/IsRCInfiniteVolumeLimitUnique.lean` is
`by exact` this theorem. -/
theorem isRCInfiniteVolumeLimit_unique {p : Set.Icc (0 : ℝ) 1} {q : Set.Ioi (0 : ℝ)} {i : Fin 2}
    {μ ν : Measure (squareLattice.edgeSet → Bool)}
    (hμ : IsRCInfiniteVolumeLimit p q i μ := by assumption)
    (hν : IsRCInfiniteVolumeLimit p q i ν := by assumption) : μ = ν :=
  WellDefined.limit_unique p q i μ ν hμ hν

end PottsContinuity.Provider
