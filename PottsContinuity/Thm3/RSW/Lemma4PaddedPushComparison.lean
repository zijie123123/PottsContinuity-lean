module

public import PottsContinuity.Thm3.Push.EnclosingComparison
public import PottsContinuity.Thm3.Push.PushOfStripRSW

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

private theorem floor_real_nat_mul (a n : ℕ) :
    ⌊(a:ℝ)*(n:ℝ)⌋ = (a:ℤ)*(n:ℤ) := by
  rw [← Nat.cast_mul,Int.floor_natCast,Nat.cast_mul]

/-- The padded comparison has enough horizontal and vertical room at every
positive nonsingleton scale, including odd scales with their actual floors. -/
theorem lemma4_padded_room (n : ℕ) (hn : 2 ≤ n) :
    56*(n:ℤ)+1 ≤ 180*(n/2:ℕ) ∧ 54*(n:ℤ) ≤ 180*(n/2:ℕ) ∧ n/2 ≤ n-1 := by
  have hnmod := Nat.mod_lt n (by omega : 0 < 2)
  have hnrepr := Nat.mod_add_div n 2
  omega

/-- The large padded push rectangle dominates the symmetric dual-reference
rectangle after actual path clipping and the proved boundary comparison. -/
theorem lemma4_padded_push_le_symmetric_reference (q : Set.Ici (1:ℝ))
    (n : ℕ) (hn : 2 ≤ n) :
    selfDualTopWiredCrossingProbability q 180 180 (n/2) ≤
    selfDualTopWiredCrossingProbability q
      ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) := by
  have hnpos : (0:ℝ) < (n-1:ℕ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hncast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hk : 0 ≤ (56*(n:ℝ)+1)/(n-1:ℕ) := div_nonneg (by positivity) hnpos.le
  have hℓ : 1 ≤ (54*(n:ℝ))/(n-1:ℕ) := by
    rw [le_div_iff₀ hnpos,one_mul,hncast]
    have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hw : ⌊((56*(n:ℝ)+1)/(n-1:ℕ))*((n-1:ℕ):ℝ)⌋ = 56*(n:ℤ)+1 := by
    rw [div_mul_cancel₀ _ hnpos.ne']
    rw [Int.floor_add_one]
    exact congrArg (fun z : ℤ => z+1) (floor_real_nat_mul 56 n)
  have hh : ⌊((54*(n:ℝ))/(n-1:ℕ))*((n-1:ℕ):ℝ)⌋ = 54*(n:ℤ) := by
    rw [div_mul_cancel₀ _ hnpos.ne']
    exact floor_real_nat_mul 54 n
  have hp : ⌊(180:ℝ)*(n/2:ℕ)⌋ = 180*(n/2:ℕ) := floor_real_nat_mul 180 (n/2)
  have hr := lemma4_padded_room n hn
  exact Push.top_wired_enclosing_comparison (selfDualParameters q) _ _ _ _ _ _ hk hℓ hr.2.2
    (by rw [hw,hp]; exact hr.1) (by rw [hh,hp]; exact hr.2.1)

end PottsContinuity.RSW
