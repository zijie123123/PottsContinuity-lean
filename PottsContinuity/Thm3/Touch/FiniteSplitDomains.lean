module

public import PottsContinuity.Thm3.Touch.FiniteStripPrimalEvents

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.Thm3.Prop4

noncomputable section

abbrev TiltedColumnVertex (n L : ℕ) (t : ℝ) :=
  (tiltedColumnWindow (2*n) L t : Set (ℤ × ℤ))

/-- The actual left subdomain, as a subset of the lattice. -/
def tiltedColumnLeftHalfDomain (n L : ℕ) (t : ℝ) : Set (ℤ × ℤ) :=
  {z | z ∈ (tiltedColumnWindow (2*n) L t : Set (ℤ × ℤ)) ∧ z.1 ≤ 0}

/-- The induced lattice graph on the left half. -/
abbrev tiltedColumnLeftHalfGraph (n L : ℕ) (t : ℝ) :=
  squareLattice.induce (tiltedColumnLeftHalfDomain n L t)

/-- Membership in the left half is the column cut of the finite strip. -/
theorem mem_tiltedColumnLeftHalfDomain (n L : ℕ) (t : ℝ) (z : ℤ × ℤ) :
    z ∈ tiltedColumnLeftHalfDomain n L t ↔
      z ∈ (tiltedColumnWindow (2*n) L t : Set (ℤ × ℤ)) ∧ z.1 ≤ 0 := Iff.rfl

end

end PottsContinuity.Thm3.Touch
