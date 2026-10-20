module

public import PottsContinuity.Thm3.Push.RectangleGeometry

@[expose] public section

namespace PottsContinuity.Push

/-- At scales divisible by three the printed n/3 translation has no rounding
error, for every real height parameter. -/
theorem floor_height_add_third_mul_three (ℓ : ℝ) (m : ℕ) :
    ⌊(ℓ + 1 / 3) * (3 * m : ℕ)⌋ = ⌊ℓ * (3 * m : ℕ)⌋ + (m : ℤ) := by
  have heq : (ℓ + 1 / 3) * ((3 * m : ℕ) : ℝ) =
      ℓ * ((3 * m : ℕ) : ℝ) + (m : ℝ) := by
    push_cast
    ring
  rw [heq, Int.floor_add_natCast]

theorem floor_four_thirds_mul_three (m : ℕ) :
    ⌊(4 / 3 : ℝ) * (3 * m : ℕ)⌋ = (4 * m : ℕ) := by
  have h : (4 / 3 : ℝ) * ((3 * m : ℕ) : ℝ) = ((4 * m : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h, Int.floor_natCast]

/-- Rounding a scale down to a positive multiple of three loses at most a
factor of two. This is the scale comparison used by an all-scale reduction. -/
theorem three_mul_div_three_bounds (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ n / 3 ∧ 3 * (n / 3) ≤ n ∧ n ≤ 2 * (3 * (n / 3)) := by
  have hr := Nat.mod_lt n (by omega : 0 < 3)
  have heq := Nat.mod_add_div n 3
  omega

end PottsContinuity.Push
