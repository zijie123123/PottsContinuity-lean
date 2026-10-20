module

public import Mathlib.Tactic
public import Mathlib.Analysis.PSeries

/-!
# Polynomial weights against stretched exponentials

DCST, the omitted analytic summation in Proposition 4, TeX line 1783.
This module proves actual summability for every positive stretched exponent,
with no recurrence or model-specific estimate as an assumption.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Any fixed real power times a positive stretched exponential tends to zero. -/
theorem tendsto_rpow_mul_stretched_exp_zero (a c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Tendsto (fun n : ℕ => (n : ℝ)^a * Real.exp (-c*(n : ℝ)^r)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/r) c hc).comp hpow
  refine h.congr' (Eventually.of_forall (fun n => ?_))
  dsimp [Function.comp_def]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  have heq : r*(a/r) = a := by field_simp
  rw [heq]

/-- Every polynomially weighted stretched-exponential series is summable.
The n=0 term is retained; the comparison with n^(-2) is only eventual. -/
theorem summable_rpow_mul_stretched_exp (a c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Summable (fun n : ℕ => (n : ℝ)^a * Real.exp (-c*(n : ℝ)^r)) := by
  have h := (tendsto_rpow_mul_stretched_exp_zero (a+2) c r hc hr).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^a * Real.exp (-c*(n : ℝ)^r) ≤ (n : ℝ)^(-2 : ℝ) := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have heq : (n : ℝ)^(a+2) * Real.exp (-c*(n : ℝ)^r) =
        ((n : ℝ)^a * Real.exp (-c*(n : ℝ)^r)) * (n : ℝ)^2 := by
      rw [Real.rpow_add hnR, Real.rpow_two]
      ring
    rw [heq] at hn
    rw [Real.rpow_neg hnR.le, Real.rpow_two, ← one_div]
    exact (le_div_iff₀ (sq_pos_of_pos hnR)).mpr hn.le
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).of_norm_bounded_eventually_nat
  filter_upwards [hbound] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a) (Real.exp_nonneg _))]
  exact hn

end PottsContinuity.Thm3.Prop4
