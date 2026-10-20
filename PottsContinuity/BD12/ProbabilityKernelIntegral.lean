module

public import PottsContinuity.BD12.ProbabilityKernelBind
public import PottsContinuity.BD12.HarrisOneDimensional

/-! Bounded real observable integrals for measurable probability kernels.
This supplies the real-valued tower calculation without assuming conditional
expectation or any marginal identity. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- A bounded nonnegative observable has a finite lower integral in every
probability law. -/
theorem unit_observable_lintegral_le_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → ℝ)
    (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _x, (1 : ENNReal) ∂μ :=
      lintegral_mono (fun x => by simpa using ENNReal.ofReal_le_ofReal (hg01 x).2)
    _ = 1 := by simp

/-- Real expectations of a bounded observable are measurable in a probability
kernel parameter. -/
theorem probabilityKernel_unit_integral_measurable {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (K : Ω → Measure α) [∀ u, IsProbabilityMeasure (K u)] (hK : Measurable K)
    (g : α → ℝ) (hg : Measurable g) (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (fun u => ∫ x, g x ∂K u) := by
  have heq (u : Ω) : (∫ x, g x ∂K u) = (∫⁻ x, ENNReal.ofReal (g x) ∂K u).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => (hg01 x).1))
      hg.aestronglyMeasurable
  simp_rw [heq]
  exact ((Measure.measurable_lintegral hg.ennreal_ofReal).comp hK).ennreal_toReal

/-- A bounded real observable can be averaged in either order through a
measurable probability kernel. -/
theorem probabilityKernel_unit_integral_bind {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Measure α) [∀ u, IsProbabilityMeasure (K u)] (hK : Measurable K)
    (g : α → ℝ) (hg : Measurable g) (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u, ∫ x, g x ∂K u ∂μ) = ∫ x, g x ∂μ.bind K := by
  let J := fun u => ∫⁻ x, ENNReal.ofReal (g x) ∂K u
  have hJ : Measurable J := (Measure.measurable_lintegral hg.ennreal_ofReal).comp hK
  have hJfin (u : Ω) : J u ≠ ⊤ :=
    ne_of_lt ((unit_observable_lintegral_le_one (K u) g hg01).trans_lt (by simp))
  have heq (u : Ω) : (∫ x, g x ∂K u) = (J u).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => (hg01 x).1))
      hg.aestronglyMeasurable
  calc
    _ = ∫ u, (J u).toReal ∂μ := by simp_rw [heq]
    _ = (∫⁻ u, ENNReal.ofReal ((J u).toReal) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun u => ENNReal.toReal_nonneg))
        hJ.ennreal_toReal.aestronglyMeasurable
    _ = (∫⁻ u, J u ∂μ).toReal := by simp_rw [ENNReal.ofReal_toReal (hJfin _)]
    _ = _ := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => (hg01 x).1)) hg.aestronglyMeasurable,
        Measure.lintegral_bind hK.aemeasurable hg.ennreal_ofReal.aemeasurable]

end
end PottsContinuity.BD12
