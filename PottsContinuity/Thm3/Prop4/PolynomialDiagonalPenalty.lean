module

public import PottsContinuity.Thm3.Prop4.SmallScale
public import PottsContinuity.Thm3.Prop4.StretchedSummability

@[expose] public section

open Filter Topology
namespace PottsContinuity.Thm3.Prop4

/-- A genuine polynomial lower bound makes the diagonal term dominate one
at every positive scale, with one coefficient for the chosen exponent. -/
theorem exists_diagonal_penalty_of_polynomial_lower
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (d β : ℝ) (hd : 0 < d)
    (hpoly : ∀ n : ℕ, 1 ≤ n → d ≤ (n : ℝ)^β*a n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → 1 ≤ Real.exp (C*(n : ℝ)^ε)*(a n)^2 := by
  have hlim := (tendsto_rpow_mul_stretched_exp_zero (2*β) 1 ε zero_lt_one hε).eventually
    (gt_mem_nhds (sq_pos_of_pos hd))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlim
  obtain ⟨C₀,hC₀,hfinite⟩ := finite_diagonal_penalty a ha ε N
  let C := max 1 C₀
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hmono (c : ℝ) (hc : c ≤ C) (n : ℕ) :
      Real.exp (c*(n : ℝ)^ε)*(a n)^2 ≤ Real.exp (C*(n : ℝ)^ε)*(a n)^2 :=
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg n) ε)))
      (sq_nonneg _)
  refine ⟨C,hC,?_⟩
  intro n hn
  by_cases hnN : N ≤ n
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hpow : ((n : ℝ)^β)^2 = (n : ℝ)^(2*β) := by
      rw [← Real.rpow_two,← Real.rpow_mul hnpos.le]
      congr 1
      ring
    have hsquare : d^2 ≤ (n : ℝ)^(2*β)*(a n)^2 := by
      calc
        _ ≤ ((n : ℝ)^β*a n)^2 := pow_le_pow_left₀ hd.le (hpoly n hn) 2
        _ = _ := by rw [mul_pow,hpow]
    have hsmall : (n : ℝ)^(2*β)*Real.exp (-(n : ℝ)^ε) ≤ d^2 := by
      simpa only [neg_mul,one_mul] using (hN n hnN).le
    have hcancel : Real.exp (-(n : ℝ)^ε) ≤ (a n)^2 :=
      le_of_mul_le_mul_left (hsmall.trans hsquare) (Real.rpow_pos_of_pos hnpos (2*β))
    have htail : 1 ≤ Real.exp ((n : ℝ)^ε)*(a n)^2 := by
      calc
        1 = Real.exp ((n : ℝ)^ε)*Real.exp (-(n : ℝ)^ε) := by rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hcancel (Real.exp_nonneg _)
    exact htail.trans (by simpa only [one_mul] using hmono 1 (le_max_left _ _) n)
  · exact (hfinite n hn (by omega)).trans (hmono C₀ (le_max_right _ _) n)

end PottsContinuity.Thm3.Prop4
