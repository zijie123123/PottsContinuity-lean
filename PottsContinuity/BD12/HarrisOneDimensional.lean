module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic

/-! One-dimensional Harris association, the base case for the product-uniform
FKG inequality needed in DRT's hybrid coupling. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

theorem integrable_of_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound x).1]
    exact (hbound x).2)

/-- Bounded increasing functions of one real random variable are positively
associated under every probability law, without a density hypothesis. -/
theorem harris_one_dimensional (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hg01 : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hfi := integrable_of_unit_bounds μ hf.measurable hf01
  have hgi := integrable_of_unit_bounds μ hg.measurable hg01
  have hfg01 : ∀ x, f x * g x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨mul_nonneg (hf01 x).1 (hg01 x).1,
      (mul_le_mul_of_nonneg_right (hf01 x).2 (hg01 x).1).trans (by simpa using (hg01 x).2)⟩
  have hfgi := integrable_of_unit_bounds μ (hf.measurable.mul hg.measurable) hfg01
  have hpoint (x y : ℝ) : 0 ≤ (f x - f y) * (g x - g y) := by
    rcases le_total y x with h | h
    · exact mul_nonneg (sub_nonneg.mpr (hf h)) (sub_nonneg.mpr (hg h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr (hg h))
  have hinner (x : ℝ) : 0 ≤ f x * g x - f x * (∫ y, g y ∂μ) -
      (∫ y, f y ∂μ) * g x + (∫ y, f y * g y ∂μ) := by
    have h := integral_nonneg (μ := μ)
      (f := fun y : ℝ => (f x - f y) * (g x - g y)) (hpoint x)
    have heq : (∫ y, (f x - f y) * (g x - g y) ∂μ) =
        f x * g x - f x * (∫ y, g y ∂μ) -
          (∫ y, f y ∂μ) * g x + (∫ y, f y * g y ∂μ) := by
      calc
        _ = ∫ y, (f x * g x - f x * g y - f y * g x) + f y * g y ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => by ring)
        _ = _ := by
          rw [integral_add (f := fun y => f x * g x - f x * g y - f y * g x)
            (g := fun y => f y * g y) (((integrable_const (f x * g x)).sub
            (hgi.const_mul (f x))).sub (hfi.mul_const (g x))) hfgi,
            integral_sub (f := fun y => f x * g x - f x * g y) (g := fun y => f y * g x)
              ((integrable_const (f x * g x)).sub (hgi.const_mul (f x)))
              (hfi.mul_const (g x)),
            integral_sub (f := fun _ => f x * g x) (g := fun y => f x * g y)
              (integrable_const (f x * g x)) (hgi.const_mul (f x)),
            integral_const_mul (f x) g, integral_mul_const (g x) f]
          simp
    rwa [heq] at h
  have houter := integral_nonneg (μ := μ)
    (f := fun x : ℝ => f x * g x - f x * (∫ y, g y ∂μ) -
      (∫ y, f y ∂μ) * g x + (∫ y, f y * g y ∂μ)) hinner
  rw [integral_add
      (f := fun x => f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x)
      (g := fun _ => ∫ y, f y * g y ∂μ)
      ((hfgi.sub (hfi.mul_const (∫ y, g y ∂μ))).sub
      (hgi.const_mul (∫ y, f y ∂μ))) (integrable_const (∫ y, f y * g y ∂μ)),
    integral_sub (f := fun x => f x * g x - f x * (∫ y, g y ∂μ))
      (g := fun x => (∫ y, f y ∂μ) * g x)
      (hfgi.sub (hfi.mul_const (∫ y, g y ∂μ))) (hgi.const_mul (∫ y, f y ∂μ)),
    integral_sub (f := fun x => f x * g x) (g := fun x => f x * (∫ y, g y ∂μ))
      hfgi (hfi.mul_const (∫ y, g y ∂μ)),
    integral_mul_const (∫ y, g y ∂μ) f,
    integral_const_mul (∫ y, f y ∂μ) g] at houter
  simp only [integral_const, probReal_univ, one_smul] at houter
  linarith only [houter]

end PottsContinuity.BD12
