module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PlanarMixed.Thm4SideFactor.SideFactor
public import PottsContinuity.Thm4Plane.FinalRootRoutes

/-!
# Proof of `PottsContinuity.theorem_1`

This module proves `PottsContinuity.Provider.theorem_1`, whose statement is exactly that of
`theorem_1` in `Frozen/Theorem1.lean` (with an implicit `q` and an auto-param `hq`), from the
other project modules. The proof in `Frozen/Theorem1.lean` is `by exact` this theorem; no other
module imports this one.

Proof assembly: `Thm4Plane.theorem_1_of_sideFactor` (the Edwards–Sokal reduction
`Thm1.theorem_1_of_theorem2` composed with the proof of Theorem 2) applied to the Theorem 4 side
factor `PlanarMixed.Thm4SideFactor.slitScreen_sideFactor`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.Provider

open PottsContinuity

/-- Exactly the statement of `PottsContinuity.theorem_1`, with an implicit `q` and an auto-param
`hq`, so that its proof in `Frozen/Theorem1.lean` is `by exact` this theorem. -/
theorem theorem_1 {q : ℕ} (hq : q ∈ Set.Icc 2 4 := by assumption) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧ μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) :=
  Thm4Plane.theorem_1_of_sideFactor (fun q' => PlanarMixed.Thm4SideFactor.slitScreen_sideFactor q'.1 q'.2) q hq

end PottsContinuity.Provider
