module

public import PottsContinuity.Thm3.Push.BoolUpperCylinderUniqueness
public import PottsContinuity.Thm3.Push.StripTranslationProbability
public import PottsContinuity.Thm3.Push.StripReflectionProbability

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- Horizontal translation fixes the entire actual top-only strip measure,
including events specifying both open and closed original bonds. -/
theorem strip_limit_map_translation (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ) (a : ℤ) :
    μ.map (stripTranslation n a) = μ := by
  let hprob : IsProbabilityMeasure μ := hμ.1
  apply finite_bool_measure_eq_of_upper_cylinders
  intro A
  have hA := boolConstantCylinder_isClopen A true
  have hAu : IsUpperSet {ω : RSW.StripConfiguration n | ∀ e ∈ A, ω e = true} := by
    intro ω η h hω e he
    exact Bool.le_iff_imp.mp (h e) (hω e he)
  unfold Measure.real
  rw [Measure.map_apply (stripTranslation_continuous n a).measurable hA.isOpen.measurableSet]
  exact (strip_limit_clopen_translation θ n μ hμ a _ hA hAu).symm

/-- Horizontal reflection fixes the entire actual top-only strip measure. -/
theorem strip_limit_map_reflection (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ) :
    μ.map (stripHorizontalReflection n) = μ := by
  let hprob : IsProbabilityMeasure μ := hμ.1
  apply finite_bool_measure_eq_of_upper_cylinders
  intro A
  have hA := boolConstantCylinder_isClopen A true
  unfold Measure.real
  rw [Measure.map_apply (stripHorizontalReflection_continuous n).measurable hA.isOpen.measurableSet]
  exact (strip_limit_clopen_reflection θ n μ hμ _ hA).symm

end
end PottsContinuity.Push
