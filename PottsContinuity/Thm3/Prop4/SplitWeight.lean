module

public import PottsContinuity.Thm3.Prop4.Concavity
public import PottsContinuity.Thm3.Prop4.StretchedSummability
public import PottsContinuity.Thm3.Prop4.WeightedDecay
public import Mathlib.Tactic

/-!
# The diagonal and off-diagonal weights in Proposition 4

DCST, TeX lines 1775–1783. The off-diagonal convolution has only a polynomial
penalty. The two weights are kept separate as required by the source proof.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Actual finite convolution estimate from the quantitative concavity gain. -/
theorem split_exp_sum_le {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (ε : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (2*m+1),
      if (m : ℝ)^ε ≤ k ∧ (m : ℝ)^ε ≤ (2*m-k : ℕ) then
        Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β)) else 0) ≤
      (2*(m : ℝ)+1)*Real.exp (-((2*m : ℕ) : ℝ)^β)*
        Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by
  classical
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ ∑ k ∈ Finset.range (2*m+1),
        Real.exp (-((2*m : ℕ) : ℝ)^β)*Real.exp (-(1-β)*(m : ℝ)^(ε*β)) := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs with h
      · have hsum : (k : ℝ)+((2*m-k : ℕ) : ℝ) = ((2*m : ℕ) : ℝ) := by
          exact_mod_cast (by have := Finset.mem_range.mp hk; omega : k+(2*m-k)=2*m)
        simpa only [hsum] using concavity_inequality hβ hβ1 ε (m : ℝ)
          (k : ℝ) ((2*m-k : ℕ) : ℝ) hmR h.1 h.2
      · positivity
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; ring

/-- A positive larger-power exponential defeats both a smaller-power
exponential penalty and any polynomial weight. -/
theorem summable_diagonal_weight (a C d ε β : ℝ)
    (hC : 0 < C) (hd : 0 < d) (hβ : 0 < β) (hεβ : ε < β) :
    Summable (fun m : ℕ => (m : ℝ)^a *
      Real.exp (C*(m : ℝ)^ε-d*(m : ℝ)^β)) := by
  have hsmall := eventually_rpow_le_half_mul hεβ (div_pos hd hC)
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖(m : ℝ)^a*Real.exp (C*(m : ℝ)^ε-d*(m : ℝ)^β)‖ ≤
        (m : ℝ)^a*Real.exp (-(d/2)*(m : ℝ)^β) := by
    filter_upwards [hsmall] with m hm
    have hmul := mul_le_mul_of_nonneg_left hm hC.le
    have heq : C*((d/C)/2) = d/2 := by field_simp
    have hmul' : C*(m : ℝ)^ε ≤ (d/2)*(m : ℝ)^β := by
      simpa only [← mul_assoc, heq] using hmul
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) a) (Real.exp_nonneg _))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hmul']))
      (Real.rpow_nonneg (Nat.cast_nonneg m) a)
  exact (summable_rpow_mul_stretched_exp a (d/2) β (half_pos hd) hβ).of_norm_bounded_eventually_nat
    hbound

/-- The exact positive diagonal gap created by β<1: 2-2^β>0. -/
theorem diagonal_rpow_gap_pos {β : ℝ} (hβ1 : β < 1) : 0 < 2-(2 : ℝ)^β := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hβ1
  rw [Real.rpow_one] at h
  exact sub_pos.mpr h

end PottsContinuity.Thm3.Prop4
