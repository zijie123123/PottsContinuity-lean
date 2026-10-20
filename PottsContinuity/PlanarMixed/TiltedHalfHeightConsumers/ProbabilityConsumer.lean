module

public import PottsContinuity.Thm3.Touch.InfiniteHalfHeightSlopeReflection
public import PottsContinuity.Thm3.RSW.FiniteBoundary

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers
open MeasureTheory Thm3.Prop4 Thm3.Touch
noncomputable section

/-- The exact infinite-strip half-height event `{F(0) ≤ n}` of the proof of Lemma 6 is
measurable. -/
theorem measurableSet_tiltedHalfHeight (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    MeasurableSet {ω : TiltedConfiguration (2*n) t |
      lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} := by
  rw [lowestTopConnectedHeight_half_sublevel_eq_iUnion n (by omega) t ht]
  exact MeasurableSet.iUnion fun R =>
    (isClopen_tiltedTopConnectionWithinBox n R t).isOpen.measurableSet

end
end PottsContinuity.PlanarMixed.TiltedHalfHeightConsumers
