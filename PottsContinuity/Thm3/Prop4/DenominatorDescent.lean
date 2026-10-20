module

public import PottsContinuity.Thm3.Prop4.LowestHeight

/-!
# Separate height denominator and horizontal descent radius

The source fixes denominator m. A finite slope cell may instead have a
representative denominator d≤2m. Descending integer ranks then gives radius
n*d*m, preserving a uniform polynomial candidate count.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Discrete-height descent with independent denominator d and neighbour radius m. -/
theorem local_minimum_with_denominator (F : ℤ → ℝ) (n m d : ℕ) (hd : 1 ≤ d)
    (hF : ∀ k : ℤ, ∃ j : ℕ, F k = (j : ℝ)/(d : ℝ)) (hzero : F 0 ≤ n) :
    ∃ k : ℤ, |k| ≤ (n : ℤ)*d*m ∧ F k ≤ n ∧
      ∀ j : ℤ, |j-k| ≤ (m : ℤ) → F k ≤ F j := by
  let f : ℤ → ℕ := fun k => ⌊F k*(d : ℝ)⌋₊
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : ∀ k : ℤ, (f k : ℝ) = F k*(d : ℝ) := by
    intro k
    obtain ⟨j,hj⟩ := hF k
    dsimp [f]
    rw [hj, div_mul_cancel₀ _ hdR.ne']
    simp only [Nat.floor_natCast]
  have hzeroR : (f 0 : ℝ) ≤ (n : ℝ)*d := by
    rw [hf]
    exact mul_le_mul_of_nonneg_right hzero hdR.le
  have hzeroN : f 0 ≤ n*d := by exact_mod_cast hzeroR
  obtain ⟨k, hk, hfk, hmin⟩ := exists_local_minimum_nat_height f m 0
  refine ⟨k, ?_, ?_, ?_⟩
  · have hzeroZ : (f 0 : ℤ) ≤ (n : ℤ)*d := by exact_mod_cast hzeroN
    calc
      |k| ≤ (f 0 : ℤ)*m := by simpa only [sub_zero] using hk
      _ ≤ ((n : ℤ)*d)*m := mul_le_mul_of_nonneg_right hzeroZ (Int.natCast_nonneg m)
  · have h : (f k : ℝ) ≤ (n : ℝ)*d := by exact_mod_cast hfk.trans hzeroN
    rw [hf] at h
    exact (mul_le_mul_iff_left₀ hdR).mp (by simpa only [mul_comm] using h)
  · intro j hj
    have h : (f k : ℝ) ≤ f j := by exact_mod_cast hmin j hj
    rw [hf,hf] at h
    exact (mul_le_mul_iff_left₀ hdR).mp (by simpa only [mul_comm] using h)

/-- The actual source height in S(2n,t) has a local minimum within n*d*m,
whenever t*d is integral. This includes d different from m. -/
theorem lowestTopConnectedHeight_local_minimum_denominator (n m d : ℕ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (t : ℝ) (htd : ∃ a : ℤ, t*(d : ℝ) = a)
    (ω : TiltedConfiguration (2*n) t)
    (hzero : lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n) :
    ∃ k : ℤ, |k| ≤ (n : ℤ)*d*m ∧
      lowestTopConnectedHeight (2*n) (by omega) t ω k ≤ n ∧
      ∀ j : ℤ, |j-k| ≤ (m : ℤ) →
        lowestTopConnectedHeight (2*n) (by omega) t ω k ≤
          lowestTopConnectedHeight (2*n) (by omega) t ω j :=
  local_minimum_with_denominator _ n m d hd
    (lowestTopConnectedHeight_discrete (2*n) (by omega) t ω d hd htd) hzero

end PottsContinuity.Thm3.Prop4
