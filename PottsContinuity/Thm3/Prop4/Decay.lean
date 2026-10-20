module

public import PottsContinuity.Thm3.Prop4.Recursion
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real

/-!
# Parameter choice and quantifier closure for Proposition 4

DCST (15 May 2015), TeX lines 1773 and 1820–1822. These statements are
about real sequences; no random-cluster decay upgrade is assumed or exported.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Choose the two exponents below α, one, and any positive Lemma-7 threshold. -/
theorem exists_recursion_exponents {α ε₀ : ℝ} (hα : 0 < α) (hε₀ : 0 < ε₀) :
    ∃ ε β : ℝ, 0 < ε ∧ ε < β ∧ β < α ∧ β < 1 ∧ ε < ε₀ := by
  obtain ⟨β, hβ, hβα⟩ := exists_between (lt_min hα zero_lt_one)
  obtain ⟨ε, hε, hεβ⟩ := exists_between (lt_min hβ hε₀)
  exact ⟨ε, β, hε, hεβ.trans_le (min_le_left _ _),
    hβα.trans_le (min_le_left _ _), hβα.trans_le (min_le_right _ _),
    hεβ.trans_le (min_le_right _ _)⟩

/-- Absorb a positive multiplicative prefactor into half the exponential rate. -/
theorem eventually_absorb_exponential_prefactor {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      A * Real.exp (-c * (n : ℝ)) ≤ Real.exp (-(c/2) * (n : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * Real.log A / c)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbound : 2 * Real.log A / c ≤ (n : ℝ) :=
    hN.trans (by exact_mod_cast hn)
  have hlog : 2 * Real.log A ≤ (n : ℝ) * c := (div_le_iff₀ hc).mp hbound
  rw [← Real.exp_log hA, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith only [hlog])

/-- If every positive index has value strictly below one, an eventual
exponential bound extends to all positive indices after reducing its rate. -/
theorem exponential_bound_all_positive_of_eventually
    (a : ℕ → ℝ) (hsmall : ∀ n, 1 ≤ n → a n < 1)
    (htail : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, a n ≤ Real.exp (-c*(n : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, 1 ≤ n → a n ≤ Real.exp (-c*(n : ℝ)) := by
  obtain ⟨d, hd, ht⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  obtain ⟨e, he, hbase⟩ := finite_exponential_rate a (Finset.Icc 1 N) (by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    exact ⟨hn1, hsmall n hn1⟩)
  refine ⟨min d e, lt_min hd he, ?_⟩
  intro n hn
  by_cases hnN : n ≤ N
  · exact (hbase n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)).trans
      (Real.exp_le_exp.mpr (by
        have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith only [min_le_right d e, hnR]))
  · exact (hN n (Nat.le_of_lt (Nat.lt_of_not_ge hnN))).trans
      (Real.exp_le_exp.mpr (by
        have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith only [min_le_left d e, hnR]))

/-- The corrected c₀ premise supplies the strict small-scale inequality needed
for quantifier closure, independently of the value of the real exponent. -/
theorem lt_one_of_stretched_exponential_bound
    {a c₀ α : ℝ} {n : ℕ} (hc₀ : 0 < c₀) (hn : 1 ≤ n)
    (h : a ≤ Real.exp (-c₀ * (n : ℝ)^α)) : a < 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact h.trans_lt (Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hc₀) (Real.rpow_pos_of_pos hnR α)))

end PottsContinuity.Thm3.Prop4
