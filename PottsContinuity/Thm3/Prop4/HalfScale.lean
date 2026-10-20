module

public import Mathlib.Tactic

/-!
# Corrected half-scale threshold in the all-index recursion

DCST, TeX lines 1787–1791. An even-index recursion at 2m gives the cutoff
at m, not at 2m. The corrected all-index version keeps r(floor(n/2)).
This is a sequence interpolation lemma, not a model-specific graph export.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Extend an attained even recursion using a one-step upper ratio. The
threshold is the corrected half scale and the coefficient is uniform in n. -/
theorem all_index_recursion_half_scale_of_evenRecursion
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (r : ℕ → ℕ) (hr : Monotone r)
    (C K : ℝ) (hC : 0 < C) (hK : 1 ≤ K)
    (hratio : ∀ n, u n ≤ K*u (n+1))
    (heven : ∀ m, 1 ≤ m →
      ∃ k l : ℕ, r m ≤ k ∧ r m ≤ l ∧ 2*m ≤ k+l ∧ u (2*m) ≤ C*u k*u l)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ k l : ℕ, r (n/2) ≤ k ∧ r (n/2) ≤ l ∧ n ≤ k+l ∧
      u n ≤ (K*C)*u k*u l := by
  by_cases hnEven : n%2 = 0
  · have hm : 1 ≤ n/2 := by omega
    have heq : 2*(n/2) = n := by omega
    obtain ⟨k, l, hk, hl, hsum, hbound⟩ := heven (n/2) hm
    rw [heq] at hsum hbound
    refine ⟨k, l, hk, hl, hsum, ?_⟩
    have hprod : 0 ≤ C*u k*u l := mul_nonneg (mul_nonneg hC.le (hu k)) (hu l)
    calc
      u n ≤ C*u k*u l := hbound
      _ ≤ K*(C*u k*u l) := le_mul_of_one_le_left hprod hK
      _ = (K*C)*u k*u l := by ring
  · let m := n/2+1
    have hm : 1 ≤ m := by dsimp [m]; omega
    have heq : 2*m = n+1 := by dsimp [m]; omega
    obtain ⟨k, l, hk, hl, hsum, hbound⟩ := heven m hm
    rw [heq] at hsum hbound
    have hcut : r (n/2) ≤ r m := hr (by dsimp [m]; omega)
    refine ⟨k, l, hcut.trans hk, hcut.trans hl, by omega, ?_⟩
    calc
      u n ≤ K*u (n+1) := hratio n
      _ ≤ K*(C*u k*u l) :=
        mul_le_mul_of_nonneg_left hbound (zero_le_one.trans hK)
      _ = (K*C)*u k*u l := by ring

end PottsContinuity.Thm3.Prop4
