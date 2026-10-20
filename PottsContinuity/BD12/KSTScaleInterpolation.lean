module

public import PottsContinuity.BD12.KSTScales
public import Mathlib.Data.Nat.Log

/-! Geometric-scale selection for the source integral KST sequence. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- Every height beyond the initial scale contains a geometric-scale crossing
whose width reaches twice the target height. -/
theorem kst_scale_near_height (n : ℕ) (hn : 1536 ≤ n) :
    ∃ j : ℕ, 2*kstScale (1+j) ≤ n ∧ n < 8*kstScale (1+j) := by
  let j := Nat.log 4 (n/1536)
  have hk : n/1536 ≠ 0 := by omega
  have hlo := Nat.pow_log_le_self 4 hk
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 4) (n/1536)
  have hm : kstScale (1+j) = 768*4^j := by
    simp only [kstScale,pow_add]
    norm_num
    ring
  refine ⟨j,?_,?_⟩
  · rw [hm]
    have hdiv := Nat.mul_div_le n 1536
    change 4^j ≤ n/1536 at hlo
    omega
  · rw [hm]
    change n/1536 < 4^(j+1) at hhi
    rw [pow_succ] at hhi
    omega

end PottsContinuity.BD12
