module

public import PottsContinuity.Thm3.RSW.Analytic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-!
# The exact geometric-scale exponent in Proposition 3

DCST eqs. (18)–(19): a sevenfold squaring recursion gives stretched exponential
decay on its geometric ladder, with exponent log(2)/log(7). The proof handles
zero values of the sequence by using a strictly positive upper envelope below one.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- The source's geometric-scale decay exponent. -/
noncomputable def sevenfoldExponent : ℝ := Real.log 2 / Real.log 7

/-- The source exponent is strictly positive. -/
theorem sevenfoldExponent_pos : 0 < sevenfoldExponent :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- It is a genuine stretched exponent, strictly below one. -/
theorem sevenfoldExponent_lt_one : sevenfoldExponent < 1 := by
  apply (div_lt_one (Real.log_pos (by norm_num : (1:ℝ)<7))).mpr
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Raising seven to the source exponent gives exactly two. -/
theorem seven_rpow_sevenfoldExponent : (7 : ℝ)^sevenfoldExponent = 2 := by
  exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- The rpow at each sevenfold geometric scale is exactly the doubled power. -/
theorem sevenfold_scale_rpow (n₀ k : ℕ) :
    ((7^k*n₀ : ℕ) : ℝ)^sevenfoldExponent = (2 : ℝ)^k * (n₀ : ℝ)^sevenfoldExponent := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.mul_rpow (pow_nonneg (by norm_num) k) (Nat.cast_nonneg n₀)]
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤7), mul_comm (k:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤7), seven_rpow_sevenfoldExponent]

/-- The numerical content of eq. (19), conditional only on the stated
recursion and one strictly subunit starting value. -/
theorem sevenfold_ladder_decay (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hrec : ∀ n, 1 ≤ n → u (7*n) ≤ (u n)^2)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (hsmall : u n₀ < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ k : ℕ,
      u (7^k*n₀) ≤ Real.exp (-d * (((7^k*n₀ : ℕ) : ℝ)^sevenfoldExponent)) := by
  let r := (u n₀+1)/2
  have hr0 : 0 < r := by dsimp [r]; linarith only [hu n₀]
  have hr1 : r < 1 := by dsimp [r]; linarith only [hsmall]
  have hur : u n₀ ≤ r := by dsimp [r]; linarith only [hsmall]
  have hnR : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  let d := -Real.log r / (n₀ : ℝ)^sevenfoldExponent
  have hd : 0 < d := div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) (Real.rpow_pos_of_pos hnR _)
  refine ⟨d, hd, fun k => ?_⟩
  have hiter := sevenfold_recursion_iterate u hu hrec n₀ hn₀ k
  calc
    u (7^k*n₀) ≤ (u n₀)^(2^k) := hiter
    _ ≤ r^(2^k) := pow_le_pow_left₀ (hu n₀) hur _
    _ = Real.exp (((2^k : ℕ) : ℝ)*Real.log r) := by
      rw [Real.exp_nat_mul, Real.exp_log hr0]
    _ = Real.exp (-d * (((7^k*n₀ : ℕ) : ℝ)^sevenfoldExponent)) := by
      congr 1
      rw [sevenfold_scale_rpow]
      dsimp only [d]
      have hnPow : (n₀ : ℝ)^sevenfoldExponent ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
      rw [Nat.cast_pow, Nat.cast_ofNat]
      field_simp

end PottsContinuity.RSW
