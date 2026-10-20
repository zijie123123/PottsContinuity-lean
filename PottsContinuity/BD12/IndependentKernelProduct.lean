module

public import PottsContinuity.BD12.FiniteSeedWindow

/-! Independent kernel tensorization for finite output spaces. This is used
for the original sample and the all-replacement terminal hybrid. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- Independent probability kernels driven by independent inputs produce the
product of their marginal output laws. All measurability premises are explicit;
no independence or output-law conclusion is assumed. -/
theorem finiteKernel_independent_bind {α β A B : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Measure A) (L : β → Measure B)
    [∀ x, IsProbabilityMeasure (K x)] [∀ y, IsProbabilityMeasure (L y)]
    (hK : Measurable K) (hL : Measurable L)
    (hKL : Measurable (fun xy : α × β => (K xy.1).prod (L xy.2))) :
    (μ.prod ν).bind (fun xy => (K xy.1).prod (L xy.2)) =
      (μ.bind K).prod (ν.bind L) := by
  have : IsProbabilityMeasure (ν.bind L) := ⟨by
    rw [Measure.bind_apply MeasurableSet.univ hL.aemeasurable]
    simp⟩
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  have hrect : ({(a, b)} : Set (A × B)) = {a} ×ˢ {b} := by ext p; simp
  rw [hrect, Measure.bind_apply ((measurableSet_singleton a).prod (measurableSet_singleton b))
    hKL.aemeasurable, Measure.prod_prod]
  simp_rw [Measure.prod_prod]
  rw [Measure.bind_apply (measurableSet_singleton a) hK.aemeasurable,
    Measure.bind_apply (measurableSet_singleton b) hL.aemeasurable]
  exact lintegral_prod_mul
    ((Measure.measurable_coe (measurableSet_singleton a)).comp hK).aemeasurable
    ((Measure.measurable_coe (measurableSet_singleton b)).comp hL).aemeasurable

end PottsContinuity.BD12
