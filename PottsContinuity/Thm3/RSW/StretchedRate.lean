module

public import PottsContinuity.Thm3.Prop4.Recursion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real

/-!
# Removing a stretched-exponential prefactor

The corrected Proposition 3 needs a positive rate in the exponent at every
positive index. Strict subunit values supply the finitely many small scales.
-/

@[expose] public section

namespace PottsContinuity.RSW
open Filter Topology

/-- A positive prefactor is absorbed eventually without changing the exponent. -/
theorem eventually_absorb_stretched_prefactor (K d r : ℝ)
    (hK : 0 < K) (hd : 0 < d) (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop,
      K * Real.exp (-d*(n:ℝ)^r) ≤ Real.exp (-(d/2)*(n:ℝ)^r) := by
  have hpow := (tendsto_rpow_atTop hr).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  filter_upwards [hpow.eventually (eventually_ge_atTop (2*Real.log K/d))] with n hn
  have hlog := (div_le_iff₀ hd).mp hn
  change 2*Real.log K ≤ (n:ℝ)^r*d at hlog
  rw [← Real.exp_log hK, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [hlog])

/-- A prefactor bound and genuine strict subunit values give the corrected
all-positive-scale stretched-exponential form. No nonzero-value premise is
needed, and the exponent is retained whenever it is at most one. -/
theorem stretched_bound_all_positive_of_prefactor (a : ℕ → ℝ)
    (K d r : ℝ) (hK : 0 < K) (hd : 0 < d) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : ∀ n : ℕ, 1 ≤ n → a n < 1)
    (hbound : ∀ n : ℕ, 1 ≤ n → a n ≤ K*Real.exp (-d*(n:ℝ)^r)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → a n ≤ Real.exp (-c*(n:ℝ)^r) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_absorb_stretched_prefactor K d r hK hd hr)
  obtain ⟨e, he, hbase⟩ := Thm3.Prop4.finite_exponential_rate a (Finset.Icc 1 N) (by
    intro n hn
    exact ⟨(Finset.mem_Icc.mp hn).1, hsmall n (Finset.mem_Icc.mp hn).1⟩)
  refine ⟨min e (d/2), lt_min he (half_pos hd), fun n hn => ?_⟩
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (n:ℝ)^r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hnN : n ≤ N
  · calc
      a n ≤ Real.exp (-e*(n:ℝ)) := hbase n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
      _ ≤ Real.exp (-e*(n:ℝ)^r) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Real.rpow_le_self_of_one_le hnR hr1) (neg_nonpos.mpr he.le))
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith only [min_le_left e (d/2), hp])
  · exact ((hbound n hn).trans (hN n (by omega))).trans
      (Real.exp_le_exp.mpr (by nlinarith only [min_le_right e (d/2), hp]))

/-- The corresponding finite-base extension from an eventual bound. -/
theorem stretched_bound_all_positive_of_eventually (a : ℕ → ℝ)
    (d r : ℝ) (hd : 0 < d) (hr1 : r ≤ 1)
    (hsmall : ∀ n : ℕ, 1 ≤ n → a n < 1)
    (htail : ∀ᶠ n : ℕ in atTop, a n ≤ Real.exp (-d*(n:ℝ)^r)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → a n ≤ Real.exp (-c*(n:ℝ)^r) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  obtain ⟨e, he, hbase⟩ := Thm3.Prop4.finite_exponential_rate a (Finset.Icc 1 N) (by
    intro n hn
    exact ⟨(Finset.mem_Icc.mp hn).1, hsmall n (Finset.mem_Icc.mp hn).1⟩)
  refine ⟨min e d, lt_min he hd, fun n hn => ?_⟩
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ (n:ℝ)^r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hnN : n ≤ N
  · calc
      a n ≤ Real.exp (-e*(n:ℝ)) := hbase n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
      _ ≤ Real.exp (-e*(n:ℝ)^r) := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (Real.rpow_le_self_of_one_le hnR hr1) (neg_nonpos.mpr he.le))
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [min_le_left e d, hp])
  · exact (hN n (by omega)).trans
      (Real.exp_le_exp.mpr (by nlinarith only [min_le_right e d, hp]))

end PottsContinuity.RSW
