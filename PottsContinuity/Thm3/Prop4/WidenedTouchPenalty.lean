module

public import PottsContinuity.Thm3.Prop4.TouchHalfConsumer

/-!
# Absorbing the cropped-strip touch denominator at scale four n plus two

The larger crop contributes a fixed polynomial penalty, uniformly for every
positive scale. The two-arm factor is its numerical square.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A positive polynomial denominator has a uniform fractional-exponential bound. -/
theorem polynomial_denominator_exponential_lower (K : ℝ) (hK : 1 ≤ K)
    (ε : ℝ) (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(Real.log K+4/ε)*(n : ℝ)^ε) ≤ 1/(K*(n : ℝ)^4) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
  have hl := Real.log_nonneg hK
  have hlogn := Real.log_le_rpow_div hnpos.le hε
  have hlog4 : 4*Real.log (n : ℝ) ≤ (4/ε)*(n : ℝ)^ε := by
    convert mul_le_mul_of_nonneg_left hlogn (by norm_num : (0 : ℝ) ≤ 4) using 1; ring
  have hlogK : Real.log K ≤ Real.log K*(n : ℝ)^ε := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hl
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hD : 0 < K*(n : ℝ)^4 := by positivity
  have hlogD : Real.log (K*(n : ℝ)^4) ≤ (Real.log K+4/ε)*(n : ℝ)^ε := by
    rw [Real.log_mul (ne_of_gt hKpos) (by positivity),Real.log_pow]
    push_cast
    nlinarith only [hlog4,hlogK]
  calc
    _ ≤ Real.exp (-Real.log (K*(n : ℝ)^4)) := Real.exp_le_exp.mpr (by linarith only [hlogD])
    _ = _ := by rw [Real.exp_neg,Real.exp_log hD,one_div]

/-- The exact cropped-strip denominator at four n plus two loses only a
parameter-independent fractional-exponential factor. -/
theorem widened_touch_denominator_exponential_lower (ε : ℝ) (hε : 0 < ε)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(Real.log 25920+4/ε)*(n : ℝ)^ε) ≤
      1/(20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : ((4*n+2 : ℕ) : ℝ) ≤ 6*(n : ℝ) := by push_cast; linarith
  have hNpos : (0 : ℝ) < (4*n+2 : ℕ) := by positivity
  have hsq := pow_le_pow_left₀ hNpos.le hN 4
  have hD : 20*((4*n+2 : ℕ) : ℝ)^2*((4*n+2 : ℕ) : ℝ)^2 ≤ 25920*(n : ℝ)^4 := by
    nlinarith only [hsq]
  exact (polynomial_denominator_exponential_lower 25920 (by norm_num) ε hε hn).trans
    (one_div_le_one_div_of_le (by positivity) hD)

end PottsContinuity.Thm3.Prop4
