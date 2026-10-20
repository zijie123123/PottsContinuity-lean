module

public import PottsContinuity.Thm3.Touch.InfiniteTopEventCylinders
public import PottsContinuity.Thm3.Touch.InfiniteStripSlopeReflectionLimit

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open MeasureTheory
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4

noncomputable section

/-- The full half-height event has equal probabilities at opposite slopes. -/
theorem selfDualTiltedHalfHeight_real_reflection
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (selfDualTiltedStripMeasure q (2*n) (-t)).real
        {ω | lowestTopConnectedHeight (2*n) (by omega) (-t) ω 0 ≤ n} =
      (selfDualTiltedStripMeasure q (2*n) t).real
        {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} := by
  let F := tiltedStripSlopeReflectionHomeomorph (2*n) t
  let Et : Set (TiltedConfiguration (2*n) t) :=
    {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n}
  let Em : Set (TiltedConfiguration (2*n) (-t)) :=
    {ω | lowestTopConnectedHeight (2*n) (by omega) (-t) ω 0 ≤ n}
  have htNeg : -t ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases ht with ⟨htlo, hthi⟩
    constructor <;> linarith
  have hEt := lowestTopConnectedHeight_half_sublevel_eq_iUnion n (by omega) t ht
  have hEm := lowestTopConnectedHeight_half_sublevel_eq_iUnion n (by omega) (-t) htNeg
  have hpre : F ⁻¹' Em = Et := by
    change F ⁻¹' {ω | lowestTopConnectedHeight (2*n) (by omega) (-t) ω 0 ≤ n} =
      {ω | lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n}
    rw [hEm, hEt]
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨R, hR⟩
      exact ⟨R, (tiltedTopConnectionWithinBox_columnSlopeReflection_iff n R t ht ω).2 hR⟩
    · rintro ⟨R, hR⟩
      exact ⟨R, (tiltedTopConnectionWithinBox_columnSlopeReflection_iff n R t ht ω).1 hR⟩
  have hEmMeas : MeasurableSet Em := by
    change MeasurableSet {ω | lowestTopConnectedHeight (2*n) (by omega) (-t) ω 0 ≤ n}
    rw [hEm]
    exact MeasurableSet.iUnion fun R =>
      (isClopen_tiltedTopConnectionWithinBox n R (-t)).isOpen.measurableSet
  have href := selfDualTiltedStripMeasure_horizontalReflection q (2*n) t ht
  rw [← href]
  unfold Measure.real
  rw [Measure.map_apply F.measurable hEmMeas, hpre]

end

end PottsContinuity.Thm3.Touch
