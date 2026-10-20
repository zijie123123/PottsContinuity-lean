module

public import PottsContinuity.Thm3.RSW.StripVerticalSeed

@[expose] public section

namespace PottsContinuity.RSW

/-- The corrected seed union bound at the actual self-dual strip law works
also at rounded scales. The vertical crossing premise is the reflected-dual
input, and no translation invariance is used to choose the segment. -/
theorem selfDual_strip_vertical_has_rounded_band_seed
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hns : n ≤ 9*s)
    (hvertical : (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    ∃ j : Fin (18*k), 1/(36*(k:ℝ)) ≤ (selfDualStripMeasure q n).real
      (stripBandArm n (2*n) (-9*(k:ℤ)*s+(j.val:ℤ)*s)
        (-9*(k:ℤ)*s+((j.val:ℤ)+1)*s)) := by
  have hns' : (n:ℤ) ≤ 9*(s:ℤ) := by exact_mod_cast hns
  have hmul := mul_le_mul_of_nonneg_left hns' (Int.natCast_nonneg k)
  have hleft : -9*(k:ℤ)*s ≤ -(k:ℤ)*n := by
    convert neg_le_neg hmul using 1 <;> ring
  have hright : (k:ℤ)*n ≤ -9*(k:ℤ)*s+((18*k:ℕ):ℤ)*s := by
    calc
      _ ≤ (k:ℤ)*(9*(s:ℤ)) := hmul
      _ = _ := by push_cast; ring
  obtain ⟨j,hj⟩ := strip_vertical_crossing_has_band_seed n (-(k:ℤ)*n) ((k:ℤ)*n)
    (2*n) (-9*(k:ℤ)*s) (18*k) s (by omega) (by omega) hleft hright
    (selfDualStripMeasure q n) (1/2) hvertical
  have hratio : (1/2:ℝ)/(18*(k:ℝ)) = 1/(36*(k:ℝ)) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hj
  rw [hratio] at hj
  exact ⟨j,hj⟩

end PottsContinuity.RSW
