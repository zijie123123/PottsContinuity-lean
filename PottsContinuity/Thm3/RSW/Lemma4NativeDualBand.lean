module

public import PottsContinuity.Thm3.RSW.BottomCollarDualBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- A native sampled dual crossing of the normalized source band. All edges
belong to the actual residual dual graph; boundary wiring supplies no path.
The entire walk stays between the original face-base endpoints and rows. -/
def lemma4NativeDualBandEvent (n : ℕ) :
    Set (Configuration (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n))) :=
  {D | ∃ u v, ∃ p : (openGraph
      (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) D).Walk u v,
    u.val.1 = -56*(n:ℤ)-1 ∧ v.val.1 = 56*(n:ℤ) ∧
    ∀ z ∈ p.support, -56*(n:ℤ)-1 ≤ z.val.1 ∧ z.val.1 ≤ 56*(n:ℤ) ∧
      0 ≤ z.val.2 ∧ z.val.2 ≤ (n:ℤ)-1}

end PottsContinuity.RSW
