module

public import PottsContinuity.BD12.FiniteRevealKernel
public import PottsContinuity.BD12.UniformThreshold
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Realization of the actual fresh-edge conditional kernel by an independent
uniform threshold, with no abstract sampling-law assumption. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem finiteRevealBitLaw_true (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    finiteRevealBitLaw w R H e he true =
      ENNReal.ofReal (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) := by
  rw [finiteRevealBitLaw_apply]
  simp only [finiteRevealPattern, ite_true, finitePinnedMean]
  simp_rw [finitePinnedWeight_open_update w R H _ e he]

theorem finitePinnedMean_open_probability_mem_Ioo (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨finitePinnedMean_open_probability_pos w R H e he, ?_⟩
  have hsum := finitePinnedPartition_reveal w R H e he
  simp only [Fintype.sum_bool, finiteRevealPattern, Bool.false_eq_true, ite_false, ite_true] at hsum
  unfold finitePinnedMean
  simp_rw [← finitePinnedWeight_open_update w R H _ e he]
  apply (div_lt_one (finitePinnedPartition_pos w R H)).mpr
  linarith only [hsum, finitePinnedPartition_pos w (insert e R) (H.erase e)]

theorem finiteRevealBitLaw_false (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    finiteRevealBitLaw w R H e he false =
      ENNReal.ofReal (1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) := by
  have hsum := finitePinnedPartition_reveal w R H e he
  simp only [Fintype.sum_bool, finiteRevealPattern, Bool.false_eq_true, ite_false, ite_true] at hsum
  rw [finiteRevealBitLaw_apply]
  simp only [finiteRevealPattern, Bool.false_eq_true, ite_false, finitePinnedMean]
  simp_rw [← finitePinnedWeight_open_update w R H _ e he]
  congr 1
  apply (div_eq_iff (finitePinnedPartition_pos w R H).ne').mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (finitePinnedPartition_pos w R H).ne']
  linarith only [hsum]

/-- The literal uniform-threshold bit has exactly the conditional Boolean law. -/
theorem finiteUnitUniform_map_reveal (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (he : e ∉ R) :
    finiteUnitUniform.map
        (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0))) =
      (finiteRevealBitLaw w R H e he).toMeasure := by
  have hp := finitePinnedMean_open_probability_mem_Ioo w R H e he
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (finiteUniformBit_measurable _) (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b)]
  cases b
  · rw [finiteUnitUniform_threshold_false _ hp.1.le hp.2.le, finiteRevealBitLaw_false]
  · rw [finiteUnitUniform_threshold_true _ hp.1.le hp.2.le, finiteRevealBitLaw_true]

/-- Integrating any continuation against the fresh independent uniform is
identical to integrating it against the conditional Boolean kernel. -/
theorem finiteUnitUniform_bind_reveal {Ω : Type*} [MeasurableSpace Ω]
    (w : Finset E → Set.Ioi (0 : ℝ)) (R H : Finset E) (e : E) (he : e ∉ R)
    (f : Bool → Measure Ω) :
    finiteUnitUniform.bind (fun u =>
        f (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u)) =
      (finiteRevealBitLaw w R H e he).toMeasure.bind f := by
  rw [← finiteUnitUniform_map_reveal w R H e he]
  unfold Measure.bind
  rw [Measure.map_map (measurable_of_finite f) (finiteUniformBit_measurable _)]
  rfl

end
end PottsContinuity.BD12
