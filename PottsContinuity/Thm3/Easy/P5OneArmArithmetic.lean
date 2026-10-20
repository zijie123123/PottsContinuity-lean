module

public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm3.Easy

/-- The exponent supplied by the corrected dyadic estimate in Lemma 1. -/
noncomputable def dyadicOneArmExponent (c : ℝ) : ℝ :=
  -Real.log (1 - c) / (2 * Real.log 2)

theorem dyadicOneArmExponent_pos (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    0 < dyadicOneArmExponent c := by
  have hlog : Real.log (1 - c) < 0 :=
    (Real.log_neg_iff (by linarith)).2 (by linarith)
  unfold dyadicOneArmExponent
  exact div_pos (neg_pos.mpr hlog) (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

/-- The product beginning at annulus scale three has a weaker power bound.
For `n ≥ 32`, the missing first three dyadic factors are absorbed by halving
the exponent once more. -/
theorem dyadic_factor_after_scale_three_le_power
    (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (n : ℕ) (hn : 32 ≤ n) :
    (1 - c) ^ (Nat.log 2 n - 3) ≤
      Real.rpow (n : ℝ) (-(dyadicOneArmExponent c / 2)) := by
  have hlogc : Real.log (1 - c) < 0 :=
    (Real.log_neg_iff (by linarith)).2 (by linarith)
  have hL : 0 < -Real.log (1 - c) := neg_pos.mpr hlogc
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < 4 * Real.log 2 := by positivity
  have hk : 5 ≤ Nat.log 2 n := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num at hn ⊢
    omega
  have hnPow : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by omega) n
  have hlogn : Real.log (n : ℝ) ≤
      (Nat.log 2 n + 1 : ℝ) * Real.log 2 := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 n + 1)) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnPow.le)
      _ = (Nat.log 2 n + 1 : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
        norm_num [Nat.cast_add, Nat.cast_one, mul_comm]
  have hlognD : Real.log (n : ℝ) ≤
      ((Nat.log 2 n - 3 : ℕ) : ℝ) * (4 * Real.log 2) := by
    have hkNat : Nat.log 2 n + 1 ≤ 4 * (Nat.log 2 n - 3) := by omega
    have hkReal : (Nat.log 2 n + 1 : ℝ) ≤
        4 * ((Nat.log 2 n - 3 : ℕ) : ℝ) := by
      exact_mod_cast hkNat
    calc
      Real.log (n : ℝ) ≤ (Nat.log 2 n + 1 : ℝ) * Real.log 2 := hlogn
      _ ≤ (4 * ((Nat.log 2 n - 3 : ℕ) : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hkReal hlog2.le
      _ = ((Nat.log 2 n - 3 : ℕ) : ℝ) * (4 * Real.log 2) := by ring
  have hscaled : Real.log (n : ℝ) / (4 * Real.log 2) ≤
      (Nat.log 2 n - 3 : ℕ) := (div_le_iff₀ hD).2 hlognD
  have hmulAux :
      ((Nat.log 2 n - 3 : ℕ) : ℝ) * Real.log (1 - c) ≤
        Real.log (n : ℝ) *
          (-((-Real.log (1 - c)) / (4 * Real.log 2))) := by
    have hmid := mul_le_mul_of_nonneg_right hscaled hL.le
    have heq : dyadicOneArmExponent c / 2 =
        (-Real.log (1 - c)) / (4 * Real.log 2) := by
      unfold dyadicOneArmExponent
      ring
    calc
      ((Nat.log 2 n - 3 : ℕ) : ℝ) * Real.log (1 - c) =
          -(((Nat.log 2 n - 3 : ℕ) : ℝ) * (-Real.log (1 - c))) := by ring
      _ ≤ -((Real.log (n : ℝ) / (4 * Real.log 2)) *
          (-Real.log (1 - c))) := neg_le_neg hmid
      _ = Real.log (n : ℝ) *
          (-((-Real.log (1 - c)) / (4 * Real.log 2))) := by ring
  have hmul :
      ((Nat.log 2 n - 3 : ℕ) : ℝ) * Real.log (1 - c) ≤
        Real.log (n : ℝ) * (-(dyadicOneArmExponent c / 2)) := by
    have heq : dyadicOneArmExponent c / 2 =
        (-Real.log (1 - c)) / (4 * Real.log 2) := by
      unfold dyadicOneArmExponent
      ring
    simpa only [heq] using hmulAux
  rw [show (1 - c) ^ (Nat.log 2 n - 3) =
      Real.exp (((Nat.log 2 n - 3 : ℕ) : ℝ) * Real.log (1 - c)) by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
        congr 1
        ring]
  have hrpow :
      Real.rpow (n : ℝ) (-(dyadicOneArmExponent c / 2)) =
        Real.exp (Real.log (n : ℝ) * (-(dyadicOneArmExponent c / 2))) :=
    Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  rw [hrpow]
  exact Real.exp_le_exp.mpr hmul

end PottsContinuity.Thm3.Easy
