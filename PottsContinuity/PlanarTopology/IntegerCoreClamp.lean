module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Projection onto a nonempty closed integer interval. The proof parameter
ensures that the interval being projected onto exists on the whole carrier. -/
def integerIntervalClamp (lo hi : ℤ) (_h : lo ≤ hi) (x : ℤ) : ℤ :=
  max lo (min hi x)

theorem integerIntervalClamp_mem (lo hi : ℤ) (h : lo ≤ hi) (x : ℤ) :
    lo ≤ integerIntervalClamp lo hi h x ∧ integerIntervalClamp lo hi h x ≤ hi := by
  exact ⟨le_max_left _ _,max_le h ((min_le_left _ _))⟩

theorem integerIntervalClamp_fixed (lo hi : ℤ) (h : lo ≤ hi) (x : ℤ)
    (hx : lo ≤ x ∧ x ≤ hi) : integerIntervalClamp lo hi h x = x := by
  exact (show max lo (min hi x) = x by rw [min_eq_right hx.2,max_eq_right hx.1])

/-- Clamping consecutive integer coordinates of a true boundary-crossing
bond either contracts the bond, or fixes both original endpoints. -/
theorem integerIntervalClamp_consecutive (lo hi : ℤ) (h : lo ≤ hi) (x : ℤ)
    (hx : lo ≤ x ∧ x ≤ hi+1) :
    integerIntervalClamp lo hi h (x-1) = integerIntervalClamp lo hi h x ∨
      (integerIntervalClamp lo hi h (x-1) = x-1 ∧ integerIntervalClamp lo hi h x = x) := by
  by_cases hlow : x = lo
  · left
    subst x
    unfold integerIntervalClamp
    rw [min_eq_right (by omega : lo-1 ≤ hi),max_eq_left (by omega : lo-1 ≤ lo),
      min_eq_right h,max_self]
  by_cases hhigh : x = hi+1
  · left
    subst x
    unfold integerIntervalClamp
    rw [show hi+1-1 = hi by omega,min_self,max_eq_right h,
      min_eq_left (by omega : hi ≤ hi+1),max_eq_right h]
  · right
    exact ⟨integerIntervalClamp_fixed lo hi h (x-1) (by omega),
      integerIntervalClamp_fixed lo hi h x (by omega)⟩

end PottsContinuity.PlanarTopology
