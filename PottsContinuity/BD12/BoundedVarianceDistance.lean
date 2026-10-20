module

public import PottsContinuity.BD12.HarrisOneDimensional
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! The independent-copy variance bound and the elementary finite telescoping
estimate used before the OSSS revealment sum. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory

/-- Two values in the unit interval differ in absolute value by at most one. -/
theorem unit_interval_abs_sub (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : |x - y| ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith only [hx.1, hy.2], by linarith only [hx.2, hy.1]⟩⟩

/-- Variance is at most half the expected distance between independent copies
for every measurable [0,1]-valued observable. -/
theorem bounded_variance_le_independent_distance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
      (1 / 2 : ℝ) * ∫ xy, |f xy.1 - f xy.2| ∂μ.prod μ := by
  have hsq01 : ∀ x, f x ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨sq_nonneg _, by nlinarith only [(hf01 x).1, (hf01 x).2]⟩
  have hA := integrable_of_unit_bounds (μ.prod μ) ((hf.comp measurable_fst).pow_const 2)
    (fun xy => hsq01 xy.1)
  have hB := integrable_of_unit_bounds (μ.prod μ) ((hf.comp measurable_snd).pow_const 2)
    (fun xy => hsq01 xy.2)
  have hC := integrable_of_unit_bounds (μ.prod μ)
    ((hf.comp measurable_fst).mul (hf.comp measurable_snd)) (fun xy =>
      ⟨mul_nonneg (hf01 xy.1).1 (hf01 xy.2).1,
        (mul_le_mul_of_nonneg_right (hf01 xy.1).2 (hf01 xy.2).1).trans
          (by simpa using (hf01 xy.2).2)⟩)
  have heq : (∫ xy, (f xy.1 - f xy.2) ^ 2 ∂μ.prod μ) =
      2 * ((∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2) := by
    calc
      _ = ∫ xy, (f xy.1 ^ 2 + f xy.2 ^ 2) - 2 * (f xy.1 * f xy.2) ∂μ.prod μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun xy => by ring))
      _ = _ := by
        rw [integral_sub (f := fun xy : Ω × Ω => f xy.1 ^ 2 + f xy.2 ^ 2)
          (g := fun xy : Ω × Ω => 2 * (f xy.1 * f xy.2)) (hA.add hB) (hC.const_mul 2),
          integral_add (f := fun xy : Ω × Ω => f xy.1 ^ 2) (g := fun xy : Ω × Ω => f xy.2 ^ 2) hA hB,
          integral_const_mul 2 (fun xy : Ω × Ω => f xy.1 * f xy.2), integral_prod_mul f f]
        have ha : (∫ xy, f xy.1 ^ 2 ∂μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
          simpa using integral_prod_mul (μ := μ) (ν := μ) (fun x => f x ^ 2) (fun _ => (1 : ℝ))
        have hb : (∫ xy, f xy.2 ^ 2 ∂μ.prod μ) = ∫ x, f x ^ 2 ∂μ := by
          simpa using integral_prod_mul (μ := μ) (ν := μ) (fun _ => (1 : ℝ)) (fun x => f x ^ 2)
        rw [ha, hb]
        ring
  have habs01 := fun xy : Ω × Ω => unit_interval_abs_sub (f xy.1) (f xy.2) (hf01 xy.1) (hf01 xy.2)
  have habsi := integrable_of_unit_bounds (μ.prod μ)
    (continuous_abs.measurable.comp ((hf.comp measurable_fst).sub (hf.comp measurable_snd))) habs01
  have hdiffi : Integrable (fun xy : Ω × Ω => (f xy.1 - f xy.2) ^ 2) (μ.prod μ) := by
    convert (hA.add hB).sub (hC.const_mul 2) using 1
    funext xy
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Pi.mul_apply]
    ring
  have hle := integral_mono (f := fun xy : Ω × Ω => (f xy.1 - f xy.2) ^ 2)
    (g := fun xy : Ω × Ω => |f xy.1 - f xy.2|) hdiffi habsi (fun xy => by
    have h := habs01 xy
    nlinarith only [h.1, h.2, sq_abs (f xy.1 - f xy.2)])
  linarith only [hle, heq]

/-- Pointwise finite telescoping of absolute increments. -/
theorem abs_sub_le_sum_adjacent (a : ℕ → ℝ) (n : ℕ) :
    |a 0 - a n| ≤ ∑ i ∈ Finset.range n, |a (i + 1) - a i| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ |a 0 - a n| + |a n - a (n + 1)| := abs_sub_le _ _ _
      _ ≤ _ := by rw [abs_sub_comm (a n) (a (n + 1))]; exact add_le_add ih le_rfl

end PottsContinuity.BD12
