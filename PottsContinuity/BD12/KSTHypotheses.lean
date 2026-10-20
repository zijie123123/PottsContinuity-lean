module

public import PottsContinuity.Infinite.ClopenFKG
public import PottsContinuity.BD12.KSTApproximation
public import PottsContinuity.Infinite.Symmetry
public import PottsContinuity.Infinite.Translation

/-!
# KST probabilistic hypotheses for the wired law

The positively associated events here are arbitrary measurable upper events.
This verifies hypotheses of the KST theorem, not its crossing conclusion.
-/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK PD.Duality

noncomputable section

/-- The wired every-exhaustion limit is positively associated on all measurable
increasing events. Compact clopen approximation is supplied by `BD12.KSTApproximation`. -/
theorem wired_measurable_positive_association (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    {A B : Set LatticeConfiguration} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAu : IsUpperSet A) (hBu : IsUpperSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  let : IsProbabilityMeasure μ := hμ.1
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  have hcl : ∀ s t : Set LatticeConfiguration, IsClopen s → IsClopen t →
      IsUpperSet s → IsUpperSet t →
      (((ν s : NNReal) : ℝ) * ((ν t : NNReal) : ℝ) ≤ ((ν (s ∩ t) : NNReal) : ℝ)) := by
    intro s t hs ht hsu htu
    have h := Infinite.wired_infinite_FKG_clopen θ.toP θ.toQ
      (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property μ hμ s t hs ht hsu htu
    change μ s * μ t ≤ μ (s ∩ t) at h
    have hr := ENNReal.toReal_mono (measure_ne_top μ (s ∩ t)) h
    have hr' : (ν : Measure LatticeConfiguration).real s *
        (ν : Measure LatticeConfiguration).real t ≤
          (ν : Measure LatticeConfiguration).real (s ∩ t) := by
      change (μ s).toReal * (μ t).toReal ≤ (μ (s ∩ t)).toReal
      simpa only [ENNReal.toReal_mul] using hr
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hr'
  have h := KSTApproximation.probabilityMeasure_measurable_upper_fkg_of_clopen
    ν hcl hA hB hAu hBu
  have h' : (ν : Measure LatticeConfiguration).real A *
      (ν : Measure LatticeConfiguration).real B ≤
        (ν : Measure LatticeConfiguration).real (A ∩ B) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  exact h'

/-- Translation invariance, in the actual whole-plane configuration action. -/
theorem wired_translation_invariant (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) (a : LatticeVertex) :
    μ.map (latticeConfigurationTranslate a) = μ :=
  Infinite.infinite_volume_translation_invariant θ.toP θ.toQ θ.property 1 μ hμ a

end
end PottsContinuity.BD12
