module

public import PottsContinuity.BD12.SeedWindowMeasurability

/-! Probability kernel identities for finite-prefix disintegration. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- A measurable mixture of probability measures is a probability measure. -/
theorem probabilityKernel_bind_isProbability {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : α → Measure β) [∀ x, IsProbabilityMeasure (K x)] (hK : Measurable K) :
    IsProbabilityMeasure (μ.bind K) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hK.aemeasurable]
  simp

/-- A fixed independent right factor commutes with a measurable mixture. -/
theorem probabilityKernel_bind_prod_right {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : α → Measure β)
    [∀ x, IsProbabilityMeasure (K x)] (hK : Measurable K)
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    (μ.bind K).prod ν = μ.bind (fun x => (K x).prod ν) := by
  let := probabilityKernel_bind_isProbability μ K hK
  have hp := probabilityKernel_prod_measurable K (fun _ => ν) hK measurable_const
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.prod_prod, Measure.bind_apply hs hK.aemeasurable,
    Measure.bind_apply (hs.prod ht) hp.aemeasurable]
  simp only [Measure.prod_prod]
  exact (lintegral_mul_const (ν t) ((Measure.measurable_coe hs).comp hK)).symm

/-- An independent product disintegrates into the literal nested kernels. -/
theorem probabilityKernel_prod_bind {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν]
    (K : α × β → Measure γ) (hK : Measurable K) :
    (μ.prod ν).bind K = μ.bind (fun x => ν.bind (fun y => K (x, y))) := by
  rw [Measure.prod_def, Measure.bind_bind Measurable.map_prodMk_left.aemeasurable hK.aemeasurable]
  apply congrArg (Measure.bind μ)
  funext x
  unfold Measure.bind
  rw [Measure.map_map hK measurable_prodMk_left]
  rfl

/-- Averaging a prescribed first coordinate gives a fresh independent input,
even with two subsequent independent factors and a measurable output map. -/
theorem probabilityKernel_average_dirac_first {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (η : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (F : (α × β) × γ → δ) (hF : Measurable F) :
    μ.bind (fun x => (((Measure.dirac x).prod ν).prod η).map F) =
      ((μ.prod ν).prod η).map F := by
  have hK : Measurable (fun x : α => ((Measure.dirac x).prod ν).prod η) :=
    probabilityKernel_prod_measurable _ _
      (probabilityKernel_prod_measurable _ _ Measure.measurable_dirac measurable_const) measurable_const
  rw [← finiteKernel_map_bind μ _ hK F hF,
    ← probabilityKernel_bind_prod_right μ _
      (probabilityKernel_prod_measurable _ _ Measure.measurable_dirac measurable_const) η,
    ← probabilityKernel_bind_prod_right μ Measure.dirac Measure.measurable_dirac ν,
    Measure.bind_dirac]

end PottsContinuity.BD12
