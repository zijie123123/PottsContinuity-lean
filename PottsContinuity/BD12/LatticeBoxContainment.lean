module

public import PottsContinuity.BD12.LatticeRadius
public import Mathlib.Tactic

/-! Exact translated-box containments used in the wired-domain comparison. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK

/-- The sup-radius triangle inequality gives literal containment of closed boxes. -/
theorem latticeBox_subset_of_radius_add_le (c u : LatticeVertex) (r N : ℕ)
    (h : latticeRadius c u + r ≤ N) : latticeBox u r ⊆ latticeBox c N := by
  intro v hv
  apply (latticeRadius_le_iff_mem_box c v N).mp
  exact ((latticeRadius_triangle c u v).trans
    (Nat.add_le_add_left ((latticeRadius_le_iff_mem_box u v r).mpr hv) _)).trans h

/-- Every radius-2k box centred in Lambda_n lies in Lambda_2n when 2k<=n. -/
theorem latticeBox_twice_subset_outer (c : LatticeVertex) (n k : ℕ)
    (u : (latticeBox c n : Set LatticeVertex)) (hk : 2*k ≤ n) :
    latticeBox u.val (2*k) ⊆ latticeBox c (2*n) := by
  apply latticeBox_subset_of_radius_add_le
  have hu := (latticeRadius_le_iff_mem_box c u.val n).mpr u.property
  omega

end PottsContinuity.BD12
