-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverLayerDecay.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

theorem parafermionicCoverLayerFactor_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ 1 - 1 / (60 * (n : ℝ) ^ 4) ∧
      1 - 1 / (60 * (n : ℝ) ^ 4) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn4 : 1 ≤ (n : ℝ) ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hnR 4
  have hden : 0 < 60 * (n : ℝ) ^ 4 := by positivity
  have hfrac : 0 ≤ 1 / (60 * (n : ℝ) ^ 4) ∧
      1 / (60 * (n : ℝ) ^ 4) ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_iff₀ hden]
      nlinarith
  constructor <;> linarith

theorem parafermionicCoverLayerDecay (n : ℕ) (hn : 1 ≤ n) :
    (1 - 1 / (60 * (n : ℝ) ^ 4)) ^ (n ^ 5 - 1) ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn5 : 1 ≤ n ^ 5 := Nat.one_le_pow 5 n (by omega)
  have hn4 : 1 ≤ (n : ℝ) ^ 4 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num) hnR 4
  let x : ℝ := 1 / (60 * (n : ℝ) ^ 4)
  let m : ℕ := n ^ 5 - 1
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hbase : 0 ≤ 1 - x := by
    have := (parafermionicCoverLayerFactor_bounds n hn).1
    simpa [x] using this
  have hbase_exp : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hpoly : (n : ℝ) ^ 5 - 1 ≥ (n : ℝ) ^ 4 * ((n : ℝ) - 1) := by
    nlinarith [hn4]
  have hden : 0 < 60 * (n : ℝ) ^ 4 := by positivity
  have hmass : (m : ℝ) * x ≥ ((n : ℝ) - 1) / 60 := by
    dsimp [m, x]
    rw [Nat.cast_sub hn5]
    have hfrac : ((n : ℝ) ^ 5 - 1) / (60 * (n : ℝ) ^ 4) ≥
        ((n : ℝ) - 1) / 60 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 60) hden]
      nlinarith [hpoly]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfrac
  have hexp : (m : ℝ) * (-x) ≤ -((n : ℝ) - 1) / 60 := by
    nlinarith [hmass]
  calc
    (1 - x) ^ m ≤ Real.exp (-x) ^ m := pow_le_pow_left₀ hbase hbase_exp m
    _ = Real.exp ((m : ℝ) * (-x)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (-((n : ℝ) - 1) / 60) := Real.exp_le_exp.mpr hexp

end PottsContinuity.FKC.FiniteFK
