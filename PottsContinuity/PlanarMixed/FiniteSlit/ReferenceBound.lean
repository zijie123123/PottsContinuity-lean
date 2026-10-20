module

public import PottsContinuity.PlanarMixed.FiniteSlit.CrossingExtraction

/-! The uniform finite truncated-slit mixed estimate. Every duality, boundary,
carrier and crossing-existence input is discharged for this actual domain. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section

/-- The two separately wired outer arcs in D_M are joined by an actual OPEN
path with probability at least 1/(1+q^2), uniformly over every valid finite
truncation, at the explicit self-dual parameter and for every real q>=1. -/
theorem wired_arcs_lower_bound (q : Set.Ici (1 : ℝ))
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    1/(1+(q : ℝ)^2) ≤
      (measure (graph M x y) (criticalParameters q) (boundary M x y hM hy hyM)
        (arcsConnectionEvent (graph M x y) (alpha M x) (beta M x y))).toReal :=
  wired_arcs_lower_bound_of_dualExistence q M x y hM hy hyM
    (dual_crossing_exists_of_nonconnection M x y hM hy hyM)

end
end PottsContinuity.PlanarMixed.FiniteSlit
