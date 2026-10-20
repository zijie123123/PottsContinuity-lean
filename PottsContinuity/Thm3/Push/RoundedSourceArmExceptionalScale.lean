module

public import PottsContinuity.Thm3.Push.RoundedSourceArmGeometry

@[expose] public section

namespace PottsContinuity.Push

/-- Among all source rounded scales n at least nine, ten is the unique
exception to fitting the full translated arm rectangle inside the square. -/
theorem rounded_source_translated_rectangles_fit_iff (n : ℕ) (hn : 9 ≤ n) :
    11*((n+8)/9) ≤ 2*n ↔ n ≠ 10 := by
  omega

/-- The existing unshifted and translated arm estimates can use the same
rounded source square at every scale at least nine other than ten. -/
theorem rounded_source_both_rectangles_fit (n : ℕ) (hn : 9 ≤ n) (hnot : n ≠ 10) :
    9*((n+8)/9) ≤ 2*n ∧ 11*((n+8)/9) ≤ 2*n := by
  have h := (rounded_source_translated_rectangles_fit_iff n hn).mpr hnot
  omega

end PottsContinuity.Push
