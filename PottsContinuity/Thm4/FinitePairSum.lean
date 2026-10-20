module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

namespace PottsContinuity.Thm4

/-- A flag-reversing involution pairs the negative half of a signed sum with
its positive half. The predicate selecting the summation domain is invariant. -/
theorem sum_signed_eq_incoming_pairs {V R : Type*} [Fintype V] [AddCommGroup R]
    (L : Equiv.Perm V) (flag : V → Bool)
    (hflag : ∀ c, flag (L c) = !flag c) (P : V → Prop) [DecidablePred P]
    (hP : ∀ c, P (L c) ↔ P c) (F : V → R) :
    (∑ c, if P c then (if flag c then F c else -F c) else 0) =
      ∑ c, if P c ∧ flag c = true then F c - F (L c) else 0 := by
  classical
  have hsplit : ∀ c, (if P c then (if flag c then F c else -F c) else 0) =
      (if P c ∧ flag c = true then F c else 0) -
      (if P c ∧ flag c = false then F c else 0) := by
    intro c
    by_cases hp : P c <;> cases hf : flag c <;> simp [hp]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  have hneg : (∑ c, if P c ∧ flag c = false then F c else 0) =
      ∑ c, if P c ∧ flag c = true then F (L c) else 0 := by
    rw [← Equiv.sum_comp L]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hP, hflag]
    cases flag c <;> simp
  rw [hneg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

end PottsContinuity.Thm4
