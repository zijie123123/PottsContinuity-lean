module

public import PottsContinuity.BD12.HybridFamilyKernel

/-! An explicit finite independent seed space, represented as streams with a
prescribed background outside the sampled time window. The background is an
input, never a default value, and will be proved irrelevant to completed tree
outputs. Original and replacement coordinates retain their literal orientation. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Updating one stream coordinate is jointly measurable in the new value and
the old stream. -/
theorem measurable_stream_update (i : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ × ℝ) => Function.update p.2 i p.1) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases h : k = i
  · subst k
    simpa only [Function.update_self] using
      (measurable_fst : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ × ℝ) => p.1))
  · convert ((measurable_pi_apply k).comp
      (measurable_snd : Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ × ℝ) => p.2))) using 1
    funext p
    exact Function.update_of_ne h _ _

/-- Disintegrate a measurable map of two independent inputs, retaining their
original order. -/
theorem finiteKernel_prod_map {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (F : α × β → γ) (hF : Measurable F) :
    (μ.prod ν).map F = μ.bind (fun x => ν.map (fun y => F (x, y))) := by
  rw [Measure.prod_def]
  rw [finiteKernel_map_bind _ _ Measurable.map_prodMk_left F hF]
  congr 1
  funext x
  rw [Measure.map_map hF measurable_prodMk_left]
  rfl

/-- Draw independent pairs on [start,start+n). U is fixed before fixedThrough;
otherwise U and V are independent unit uniforms. Every V is a unit uniform.
All coordinates outside the finite window retain the specified background. -/
def finiteHybridSeedWindow (fixedThrough : ℕ) (fixedU : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) : ℕ → ℕ → Measure (ℕ → ℝ × ℝ)
  | _, 0 => Measure.dirac background
  | start, n + 1 =>
      (((finiteHybridAuxLaw fixedThrough fixedU start).prod finiteUnitUniform).prod
        (finiteHybridSeedWindow fixedThrough fixedU background (start + 1) n)).map
          (fun p => Function.update p.2 start p.1)

instance finiteHybridSeedWindow_isProbabilityMeasure (fixedThrough : ℕ)
    (fixedU : ℕ → ℝ) (background : ℕ → ℝ × ℝ) (start n : ℕ) :
    IsProbabilityMeasure (finiteHybridSeedWindow fixedThrough fixedU background start n) := by
  induction n generalizing start with
  | zero => dsimp [finiteHybridSeedWindow]; infer_instance
  | succ n ih =>
    let := ih (start + 1)
    dsimp only [finiteHybridSeedWindow]
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_stream_update start).aemeasurable).mpr inferInstance

end
end PottsContinuity.BD12
