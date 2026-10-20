module

public import PottsContinuity.Thm1.PottsInfiniteLimitPositive
public import PottsContinuity.Thm1.ZeroTemperature

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity

noncomputable section

/-- The frozen Potts infinite-volume measure exists for every integer `q ≥ 1`
and every nonnegative inverse temperature. -/
theorem exists_isPottsInfiniteVolumeLimit
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 ≤ β) (i : Fin q) :
    ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q β i μ := by
  by_cases hzero : β = 0
  · subst β
    exact exists_isPottsInfiniteVolumeLimit_zero q i
  · have hpositive : 0 < β := lt_of_le_of_ne hβ (Ne.symm hzero)
    exact exists_isPottsInfiniteVolumeLimit_pos q hq β hpositive i

end

end PottsContinuity.Thm1
