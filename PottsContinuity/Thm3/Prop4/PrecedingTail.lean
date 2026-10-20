module

public import Mathlib.Tactic

/-!
# Pairing odd squares with the following even square

The source remark controls side 2m-1 by side 2m, both at arm scale m.
This pairing retains that scale, without replacing it by floor(M/2).
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Exact pairing of every side length from 2n-1 onwards. -/
def precedingTailEquiv (n : ℕ) (hn : 1 ≤ n) :
    {M : ℕ // 2*n-1 ≤ M} ≃ {m : ℕ // n ≤ m} × Fin 2 where
  toFun M := (⟨(M.1+1)/2,by omega⟩,⟨(M.1+1)%2,by omega⟩)
  invFun p := ⟨2*p.1.1+p.2.1-1,by have := p.1.2; omega⟩
  left_inv M := by apply Subtype.ext; dsimp; omega
  right_inv p := by
    rcases p with ⟨⟨m,hm⟩,⟨r,hr⟩⟩
    apply Prod.ext
    · apply Subtype.ext; dsimp; omega
    · apply Fin.ext; dsimp; omega

/-- The odd/even square grouping holds for arbitrary ENNReal tails. -/
theorem tsum_precedingTail (f : ℕ → ENNReal) (n : ℕ) (hn : 1 ≤ n) :
    (∑' M : {M : ℕ // 2*n-1 ≤ M}, f M.1) =
      ∑' m : {m : ℕ // n ≤ m}, (f (2*m.1-1)+f (2*m.1)) := by
  rw [← (precedingTailEquiv n hn).symm.tsum_eq (fun M => f M.1)]
  change (∑' p : {m : ℕ // n ≤ m} × Fin 2, f (2*p.1.1+p.2.1-1)) = _
  rw [ENNReal.tsum_prod (f := fun (m : {m : ℕ // n ≤ m}) (r : Fin 2) => f (2*m.1+r.1-1))]
  apply tsum_congr
  intro m
  simp only [tsum_fintype,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.add_zero]
  congr 2

end PottsContinuity.Thm3.Prop4
