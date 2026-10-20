module

public import PottsContinuity.Thm3.Push.EnclosingComparison
public import PottsContinuity.Thm3.Push.CrossingPositivity
public import PottsContinuity.Thm3.Push.ThirdRounding

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW
noncomputable section

/-- Rounding down to a multiple of three is sound after doubling the two
aspect parameters: the comparison preserves the free bottom and clips actual
open paths. No strip or exploration estimate is used. -/
theorem selfDual_round_down_probability_le (q : Set.Ici (1 : ℝ))
    (k ℓ : ℝ) (hk : 0 ≤ k) (hℓ : 1 ≤ ℓ) (n : ℕ) (hn : 3 ≤ n) :
    selfDualTopWiredCrossingProbability q (2*k) (2*ℓ) (3*(n/3)) ≤
      selfDualTopWiredCrossingProbability q k ℓ n := by
  obtain ⟨_, hsmall, hlarge⟩ := three_mul_div_three_bounds n hn
  have hreal : (n : ℝ) ≤ 2*(3*(n/3 : ℕ) : ℕ) := by exact_mod_cast hlarge
  have hw : ⌊k*n⌋ ≤ ⌊(2*k)*(3*(n/3 : ℕ))⌋ := by
    apply Int.floor_mono
    have h := mul_le_mul_of_nonneg_left hreal hk
    push_cast at h ⊢
    nlinarith only [h]
  have hh : ⌊ℓ*n⌋ ≤ ⌊(2*ℓ)*(3*(n/3 : ℕ))⌋ := by
    apply Int.floor_mono
    have h := mul_le_mul_of_nonneg_left hreal (by linarith only [hℓ] : 0 ≤ ℓ)
    push_cast at h ⊢
    nlinarith only [h]
  exact top_wired_enclosing_comparison (selfDualParameters q) k ℓ (2*k) (2*ℓ)
    n (3*(n/3)) hk hℓ hsmall
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hw)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh)

/-- A full divisible-scale Lemma-3 estimate implies the exact all-scale
conclusion. This is only a rounding consumer, not a proof of Lemma 3: its
premise must still be supplied by the highest-crossing height induction. -/
theorem selfDual_all_scale_bound_of_divisible_bound
    (q : Set.Ici (1 : ℝ)) (k ℓ : ℝ) (hk : 0 < k) (hℓ : 4/3 ≤ ℓ)
    (hdiv : ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualTopWiredCrossingProbability q (2*k) (2*ℓ) (3*s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ selfDualTopWiredCrossingProbability q k ℓ n := by
  obtain ⟨c, hc, hbound⟩ := hdiv
  have hpos (n : ℕ) : 0 < selfDualTopWiredCrossingProbability q k ℓ n :=
    topWiredCrossing_probability_pos (selfDualParameters q) k ℓ n hk.le (by linarith only [hℓ])
  refine ⟨min c (min (selfDualTopWiredCrossingProbability q k ℓ 1)
    (selfDualTopWiredCrossingProbability q k ℓ 2)),
    lt_min hc (lt_min (hpos 1) (hpos 2)), ?_⟩
  intro n hn
  by_cases h3 : 3 ≤ n
  · exact (min_le_left _ _).trans ((hbound (n/3)
      (three_mul_div_three_bounds n h3).1).trans
      (selfDual_round_down_probability_le q k ℓ hk.le (by linarith only [hℓ]) n h3))
  · have hcases : n=1 ∨ n=2 := by omega
    rcases hcases with rfl | rfl
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)

end
end PottsContinuity.Push
