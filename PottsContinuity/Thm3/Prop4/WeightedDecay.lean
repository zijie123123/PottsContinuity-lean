module

public import Mathlib.Tactic

/-!
# Stretched-exponential decay after reweighting

DCST (15 May 2015), TeX lines 1770–1793, numeric part of the proof of
Proposition 4 that the reweighted sequence tends to zero, retaining the
corrected coefficient c₀.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The smaller power is eventually absorbed by any positive multiple of the
larger positive power. -/
theorem eventually_rpow_le_half_mul {α β c₀ : ℝ} (hβα : β < α) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^β ≤ (c₀/2)*(n : ℝ)^α := by
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)^(β-α)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hβα)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, neg_sub] using h
  have hsmall := hratio.eventually (gt_mem_nhds (half_pos hc₀))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have heq : (n : ℝ)^(β-α) * (n : ℝ)^α = (n : ℝ)^β := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hnR.le α)
  rwa [heq] at h

/-- The stretched-exponential premise remains decaying after multiplying by
exp(n^β), for β<α. The sequence is generic and all hypotheses remain explicit. -/
theorem weighted_stretched_exponential_tendsto_zero
    (a : ℕ → ℝ) {α β c₀ : ℝ} (hα : 0 < α) (hβα : β < α) (hc₀ : 0 < c₀)
    (ha : ∀ n, 0 ≤ a n)
    (hdecay : ∀ n, 1 ≤ n → a n ≤ Real.exp (-c₀*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ)^β) * a n) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => Real.exp (-(c₀/2)*(n : ℝ)^α))
      atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
    have hmul := hpow.const_mul_atTop (half_pos hc₀)
    have hneg := tendsto_neg_atTop_atBot.comp hmul
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp hneg
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    mul_nonneg (Real.exp_nonneg _) (ha n))) ?_ hupper
  filter_upwards [eventually_rpow_le_half_mul hβα hc₀, eventually_ge_atTop 1]
    with n hn hn1
  calc
    Real.exp ((n : ℝ)^β) * a n ≤
        Real.exp ((n : ℝ)^β) * Real.exp (-c₀*(n : ℝ)^α) :=
      mul_le_mul_of_nonneg_left (hdecay n hn1) (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ)^β - c₀*(n : ℝ)^α) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(c₀/2)*(n : ℝ)^α) :=
      Real.exp_le_exp.mpr (by linarith only [hn])

end PottsContinuity.Thm3.Prop4
