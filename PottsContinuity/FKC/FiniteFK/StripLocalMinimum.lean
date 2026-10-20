-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/StripLocalMinimum.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- A nonnegative integer-indexed height with value at most `N` somewhere in the
sense `f 0 ≤ N` has an `m`-local minimum within distance `N*m` of the origin. -/
theorem exists_local_minimum_on_integer_strip
    (f : ℤ → ℕ) (N m : ℕ) (h0 : f 0 ≤ N) :
    ∃ k : ℤ, k.natAbs ≤ N * m ∧ f k ≤ f 0 ∧
      ∀ l : ℤ, (l - k).natAbs ≤ m → f k ≤ f l := by
  induction N generalizing f m with
  | zero =>
      have hf0 : f 0 = 0 := by omega
      refine ⟨0, by simp, ?_, ?_⟩
      · rfl
      · intro l hl
        rw [hf0]
        exact Nat.zero_le _
  | succ N ih =>
      by_cases hmin : ∀ l : ℤ, l.natAbs ≤ m → f 0 ≤ f l
      · refine ⟨0, by simp, le_rfl, ?_⟩
        intro l hl
        have hl' : l.natAbs ≤ m := by simpa using hl
        exact hmin l hl'
      · push Not at hmin
        obtain ⟨l, hl, hlt⟩ := hmin
        have hfl : f l ≤ N := by omega
        let g : ℤ → ℕ := fun j => f (j + l)
        obtain ⟨j, hj, hgj, hjlocal⟩ := ih g m (by simpa [g] using hfl)
        let k : ℤ := j + l
        refine ⟨k, ?_, ?_, ?_⟩
        · dsimp [k]
          calc
            (j + l).natAbs ≤ j.natAbs + l.natAbs := Int.natAbs_add_le _ _
            _ ≤ N * m + m := Nat.add_le_add hj hl
            _ = (N + 1) * m := by rw [Nat.add_mul]; simp
        · have hleft : f k = g j := by simp [g, k]
          have hright : g 0 = f l := by simp [g]
          calc
            f k = g j := hleft
            _ ≤ g 0 := hgj
            _ = f l := hright
            _ ≤ f 0 := Nat.le_of_lt hlt
        · intro t ht
          have hdist : (t - l - j).natAbs ≤ m := by
            have heq : t - l - j = t - (j + l) := by omega
            rw [heq]
            simpa [k] using ht
          have hlocal := hjlocal (t - l) hdist
          simpa [g, k, sub_add_cancel] using hlocal

end PottsContinuity.FKC.FiniteFK
