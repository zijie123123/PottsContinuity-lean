module

public import PottsContinuity.BD12.HarrisOneDimensional
public import Mathlib.MeasureTheory.Integral.Prod

/-! Positive association is preserved by independent products. This is the
induction step from one-dimensional Harris to finite product-uniform Harris. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

theorem integral_mem_unit_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂μ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (f := f) (fun x => (hbound x).1), ?_⟩
  calc
    _ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono
      (integrable_of_unit_bounds μ hf hbound) (integrable_const 1) (fun x => (hbound x).2)
    _ = 1 := by simp

/-- The association premises are the properties of the two factors; this
proves their product property and is used as an induction step. -/
theorem harris_tensorization {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Preorder Ω] [Preorder Ξ] (μ : Measure Ω) (ν : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ f g : Ω → ℝ, Measurable f → Measurable g → Monotone f → Monotone g →
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) →
      (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ)
    (hν : ∀ f g : Ξ → ℝ, Measurable f → Measurable g → Monotone f → Monotone g →
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) →
      (∫ x, f x ∂ν) * (∫ x, g x ∂ν) ≤ ∫ x, f x * g x ∂ν)
    (f g : Ω × Ξ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfm : Monotone f) (hgm : Monotone g)
    (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hg01 : ∀ z, g z ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, f z ∂μ.prod ν) * (∫ z, g z ∂μ.prod ν) ≤ ∫ z, f z * g z ∂μ.prod ν := by
  let F := fun x => ∫ y, f (x, y) ∂ν
  let G := fun x => ∫ y, g (x, y) ∂ν
  let H := fun x => ∫ y, f (x, y) * g (x, y) ∂ν
  have hfg01 (z : Ω × Ξ) : f z * g z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hf01 z).1 (hg01 z).1,
      (mul_le_mul_of_nonneg_right (hf01 z).2 (hg01 z).1).trans (by simpa using (hg01 z).2)⟩
  have hfx (x : Ω) : Measurable (fun y => f (x, y)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have hgx (x : Ω) : Measurable (fun y => g (x, y)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  have hF : Measurable F := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hG : Measurable G := hg.stronglyMeasurable.integral_prod_right'.measurable
  have hH : Measurable H := (hf.mul hg).stronglyMeasurable.integral_prod_right'.measurable
  have hF01 (x : Ω) : F x ∈ Set.Icc (0 : ℝ) 1 :=
    integral_mem_unit_interval ν (hfx x) (fun y => hf01 (x, y))
  have hG01 (x : Ω) : G x ∈ Set.Icc (0 : ℝ) 1 :=
    integral_mem_unit_interval ν (hgx x) (fun y => hg01 (x, y))
  have hH01 (x : Ω) : H x ∈ Set.Icc (0 : ℝ) 1 :=
    integral_mem_unit_interval ν ((hfx x).mul (hgx x)) (fun y => hfg01 (x, y))
  have hFm : Monotone F := by
    intro x x' hxx'
    exact integral_mono
      (integrable_of_unit_bounds ν (hfx x) (fun y => hf01 (x, y)))
      (integrable_of_unit_bounds ν (hfx x') (fun y => hf01 (x', y)))
      (fun y => hfm (show (x, y) ≤ (x', y) from ⟨hxx', le_rfl⟩))
  have hGm : Monotone G := by
    intro x x' hxx'
    exact integral_mono
      (integrable_of_unit_bounds ν (hgx x) (fun y => hg01 (x, y)))
      (integrable_of_unit_bounds ν (hgx x') (fun y => hg01 (x', y)))
      (fun y => hgm (show (x, y) ≤ (x', y) from ⟨hxx', le_rfl⟩))
  have hsection (x : Ω) : F x * G x ≤ H x :=
    hν _ _ (hfx x) (hgx x)
      (fun y y' hyy' => hfm (show (x, y) ≤ (x, y') from ⟨le_rfl, hyy'⟩))
      (fun y y' hyy' => hgm (show (x, y) ≤ (x, y') from ⟨le_rfl, hyy'⟩))
      (fun y => hf01 (x, y)) (fun y => hg01 (x, y))
  have hFG01 (x : Ω) : F x * G x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hF01 x).1 (hG01 x).1,
      (mul_le_mul_of_nonneg_right (hF01 x).2 (hG01 x).1).trans (by simpa using (hG01 x).2)⟩
  have hprod := integral_mono
    (integrable_of_unit_bounds μ (hF.mul hG) hFG01)
    (integrable_of_unit_bounds μ hH hH01) hsection
  rw [integral_prod _ (integrable_of_unit_bounds (μ.prod ν) hf hf01),
    integral_prod _ (integrable_of_unit_bounds (μ.prod ν) hg hg01),
    integral_prod (fun z => f z * g z)
      (integrable_of_unit_bounds (μ.prod ν) (hf.mul hg) hfg01)]
  exact (hμ F G hF hG hFm hGm hF01 hG01).trans hprod

end PottsContinuity.BD12
