module

public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.RSW

/-- Closed adjacent segments include the last endpoint as well as every
interior integer. No divisibility of the covered point is required. -/
theorem nat_interval_covered_by_adjacent_segments (N s z : ℕ)
    (hN : 0 < N) (hs : 0 < s) (hz : z ≤ N*s) :
    ∃ j : Fin N, j.val*s ≤ z ∧ z ≤ (j.val+1)*s := by
  by_cases heq : z = N*s
  · refine ⟨⟨N-1,by omega⟩,?_,?_⟩
    · change (N-1)*s ≤ z
      have h := Nat.mul_le_mul_right s (show N-1 ≤ N from Nat.sub_le _ _)
      omega
    · change z ≤ (N-1+1)*s
      have h : N-1+1 = N := by omega
      rw [h]
      exact hz
  · have hlt : z < N*s := by omega
    have hdiv : z/s < N := (Nat.div_lt_iff_lt_mul hs).mpr hlt
    refine ⟨⟨z/s,hdiv⟩,Nat.div_mul_le_self z s,?_⟩
    change z ≤ (z/s+1)*s
    have hrem := Nat.mod_lt z hs
    have he := Nat.mod_add_div z s
    rw [Nat.mul_comm s (z/s)] at he
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Integer translation of the exact adjacent-segment cover. -/
theorem int_interval_covered_by_adjacent_segments (N s : ℕ) (A z : ℤ)
    (hN : 0 < N) (hs : 0 < s) (hz0 : A ≤ z) (hzN : z ≤ A+N*s) :
    ∃ j : Fin N, A+(j.val:ℤ)*s ≤ z ∧ z ≤ A+((j.val:ℤ)+1)*s := by
  have hd : 0 ≤ z-A := by omega
  let d := (z-A).toNat
  have hdeq : (d:ℤ) = z-A := Int.toNat_of_nonneg hd
  have hdN : d ≤ N*s := by exact_mod_cast (by omega : (d:ℤ) ≤ (N:ℤ)*s)
  obtain ⟨j,hj0,hj1⟩ := nat_interval_covered_by_adjacent_segments N s d hN hs hdN
  have hj0' : (j.val:ℤ)*s ≤ d := by exact_mod_cast hj0
  have hj1' : (d:ℤ) ≤ ((j.val:ℤ)+1)*s := by exact_mod_cast hj1
  exact ⟨j,by omega,by omega⟩

end PottsContinuity.RSW
