module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Numeric leaves for the P4 to P5 argument

Source: DCST (15 May 2015), proof of Proposition 3, TeX lines 1519–1527,
and the assembly of P4 to P5 at line 1544. These are numeric helper lemmas;
they do not assert the random-cluster recursion or the decay upgrade.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.RSW

/-- Iteration of the sevenfold squaring recursion, the numeric part of eq:18.
The nonnegative sequence and its recursion are explicit inputs to this helper. -/
theorem sevenfold_recursion_iterate (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hrec : ∀ n, 1 ≤ n → u (7 * n) ≤ (u n) ^ 2)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (k : ℕ) :
    u (7 ^ k * n₀) ≤ (u n₀) ^ (2 ^ k) := by
  induction k with
  | zero => simp only [pow_zero, one_mul, pow_one, le_refl]
  | succ k ih =>
    have hscale : 1 ≤ 7 ^ k * n₀ :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by decide))
        (Nat.ne_of_gt hn₀))
    calc
      u (7 ^ (k + 1) * n₀) = u (7 * (7 ^ k * n₀)) := by
        congr 1
        rw [pow_succ]
        ring
      _ ≤ (u (7 ^ k * n₀)) ^ 2 := hrec _ hscale
      _ ≤ ((u n₀) ^ (2 ^ k)) ^ 2 := pow_le_pow_left₀ (hu _) ih 2
      _ = (u n₀) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

/-- Exponential decay bounds the normalized logarithm away from zero.
Strict positivity is necessary because `Real.log 0 = 0`. -/
theorem log_rate_le_of_exponential_bound {a c : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < a) (hdecay : a ≤ Real.exp (-c * (n : ℝ))) :
    1 / (n : ℝ) * Real.log a ≤ -c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog : Real.log a ≤ -c * (n : ℝ) :=
    (Real.log_le_iff_le_exp ha).mpr hdecay
  calc
    1 / (n : ℝ) * Real.log a ≤ 1 / (n : ℝ) * (-c * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = -c := by field_simp

/-- The analytic contradiction used at the end of P4 to P5. Positivity and
exponential decay need hold only eventually; no model-specific input is hidden. -/
theorem not_exponential_decay_of_log_rate_zero (a : ℕ → ℝ)
    (hpos : ∀ᶠ n in atTop, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.log (a n)) atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, a n ≤ Real.exp (-c * (n : ℝ)) := by
  rintro ⟨c, hc, hdecay⟩
  have hbound : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) * Real.log (a n) ≤ -c := by
    filter_upwards [hpos, hdecay, eventually_ge_atTop 1] with n hnpos hndecay hn
    exact log_rate_le_of_exponential_bound hn hnpos hndecay
  have hlim : (0 : ℝ) ≤ -c := le_of_tendsto hrate hbound
  linarith only [hlim, hc]

end PottsContinuity.RSW
