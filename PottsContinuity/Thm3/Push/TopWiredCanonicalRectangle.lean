module

public import PottsContinuity.Thm3.Push.ThirdRounding
public import PottsContinuity.Foundations.HorizontalCrossingBridge

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- On the intended nonnegative-aspect range, the literal floor rectangle
has exactly this PD vertex carrier. No fallback carrier is defined outside
that range. -/
theorem topWiredRectangle_eq_canonical (k ℓ : ℝ) (n : ℕ) (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) :
    PD.FK.latticeRectangle (-⌊k*n⌋,0) (⌊k*n⌋- -⌊k*n⌋).toNat ⌊ℓ*n⌋.toNat =
      RSW.topWiredRectangle k ℓ n := by
  have hw : 0 ≤ ⌊k*n⌋ := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  have hh : 0 ≤ ⌊ℓ*n⌋ := Int.floor_nonneg.mpr (mul_nonneg hℓ (Nat.cast_nonneg n))
  simpa only [sub_zero,RSW.topWiredRectangle] using
    (Foundations.pdRectangle_eq_frozenRectangle_of_corners (-⌊k*n⌋) ⌊k*n⌋ 0 ⌊ℓ*n⌋ (by omega) hh)

/-- Exact reference height at the approved divisible scales. -/
theorem topWiredRectangle_base_three_eq_canonical (k : ℝ) (s : ℕ) (hk : 0 ≤ k) :
    PD.FK.latticeRectangle (-⌊k*(3*s : ℕ)⌋,0)
      (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s) =
      RSW.topWiredRectangle k (4/3) (3*s) := by
  have heq := topWiredRectangle_eq_canonical k (4/3) (3*s) hk (by norm_num)
  rw [floor_four_thirds_mul_three] at heq
  simpa only [Int.toNat_natCast] using heq

/-- The canonical reference width has precisely the original two floor
side coordinates, including a zero-width domain. -/
theorem topWired_canonical_right_coordinate (k : ℝ) (n : ℕ) (hk : 0 ≤ k) :
    -⌊k*n⌋ + ((⌊k*n⌋- -⌊k*n⌋).toNat : ℤ)=⌊k*n⌋ := by
  have hw : 0 ≤ ⌊k*n⌋ := Int.floor_nonneg.mpr (mul_nonneg hk (Nat.cast_nonneg n))
  rw [Int.toNat_of_nonneg (by omega)]
  omega

end
end PottsContinuity.Push
