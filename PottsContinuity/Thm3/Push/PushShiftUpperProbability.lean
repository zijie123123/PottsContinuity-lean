module

public import PottsContinuity.Thm3.Push.PushShiftCrossingTransport

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- The exact outer upper-band probability dominates the induction crossing
probability. This combines the proved original-boundary comparison and the
literal shift of every sampled open path vertex, at arbitrary Parameters. -/
theorem pushShift_upper_band_probability_ge (θ : Parameters) (k ℓ : ℝ) (s : ℕ) :
    finiteBoundaryEventProbability (topWiredRectangle k ℓ (3*s)) θ
      (topWiredRectangleBoundary k ℓ (3*s))
      (horizontalCrossing (topWiredRectangle k ℓ (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ)) ≤
    finiteBoundaryEventProbability (topWiredRectangle k (ℓ+1/3) (3*s)) θ
      (topWiredRectangleBoundary k (ℓ+1/3) (3*s))
      (horizontalCrossing (topWiredRectangle k (ℓ+1/3) (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ s (4*s : ℕ)) := by
  let S := topWiredRectangle k ℓ (3*s)
  let E := finiteBoolEvent S (horizontalCrossing S (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ))
  have hE : IsUpperSet E := finiteBoolEvent_isUpperSet S _ (horizontalCrossing_isUpperSet S _ _ _ _)
  have hshift := pushShift_restriction_probability_ge θ k ℓ s E hE
  apply hshift.trans
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro A hA
  exact shifted_restricted_crossing_implies_upper_band k ℓ s A hA

/-- Explicit self-dual specialization for every real q>=1. -/
theorem selfDual_probability_le_shifted_upper_band (q : Set.Ici (1 : ℝ)) (k ℓ : ℝ) (s : ℕ) :
    selfDualTopWiredCrossingProbability q k ℓ (3*s) ≤
    finiteBoundaryEventProbability (topWiredRectangle k (ℓ+1/3) (3*s)) (selfDualParameters q)
      (topWiredRectangleBoundary k (ℓ+1/3) (3*s))
      (horizontalCrossing (topWiredRectangle k (ℓ+1/3) (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ s (4*s : ℕ)) :=
  pushShift_upper_band_probability_ge (selfDualParameters q) k ℓ s

end
end PottsContinuity.Push
