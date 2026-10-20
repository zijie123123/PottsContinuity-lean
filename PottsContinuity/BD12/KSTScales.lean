module

public import Mathlib.Tactic

/-! Integral source scales used by the shared KST corridor construction. -/

@[expose] public section

namespace PottsContinuity.BD12

def kstScale (j : ℕ) : ℕ := 192*4^j

theorem kstScale_pos (j : ℕ) : 1 ≤ kstScale j := by
  have h : 0 < (4 : ℕ)^j := pow_pos (by decide) j
  unfold kstScale
  omega

theorem kstScale_mono : Monotone kstScale := by
  intro j k hjk
  exact Nat.mul_le_mul_left 192 (Nat.pow_le_pow_right (by decide : 1 ≤ 4) hjk)

theorem kstScale_succ (j : ℕ) : kstScale (j+1) = 4*kstScale j := by
  simp only [kstScale,pow_succ]
  ring

theorem kstScale_dvd_twelve (j : ℕ) : 12 ∣ kstScale j :=
  dvd_mul_of_dvd_left (by decide : 12 ∣ 192) _

end PottsContinuity.BD12
