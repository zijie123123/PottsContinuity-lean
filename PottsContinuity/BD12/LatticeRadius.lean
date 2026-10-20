module

public import PottsContinuity.PD.FK.Lattice
public import Mathlib.Data.Nat.Dist
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Integer sup-radius of actual square-lattice vertices. These graph metric
facts supply the deterministic hypotheses of the shell-exploration estimate. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK

/-- The coordinate sup-distance, in unscaled lattice units. -/
def latticeRadius (c v : LatticeVertex) : ℕ :=
  max (v.1 - c.1).natAbs (v.2 - c.2).natAbs

@[simp] theorem latticeRadius_self (c : LatticeVertex) : latticeRadius c c = 0 := by
  simp [latticeRadius]

theorem latticeRadius_symm (u v : LatticeVertex) : latticeRadius u v = latticeRadius v u := by
  unfold latticeRadius
  omega

theorem latticeRadius_triangle (c u v : LatticeVertex) :
    latticeRadius c v ≤ latticeRadius c u + latticeRadius u v := by
  have h1 : (v.1 - c.1).natAbs ≤ (u.1 - c.1).natAbs + (v.1 - u.1).natAbs := by
    convert Int.natAbs_add_le (u.1 - c.1) (v.1 - u.1) using 1; congr 1; omega
  have h2 : (v.2 - c.2).natAbs ≤ (u.2 - c.2).natAbs + (v.2 - u.2).natAbs := by
    convert Int.natAbs_add_le (u.2 - c.2) (v.2 - u.2) using 1; congr 1; omega
  exact max_le (h1.trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (h2.trans (add_le_add (le_max_right _ _) (le_max_right _ _)))

theorem latticeRadius_le_iff_mem_box (c v : LatticeVertex) (n : ℕ) :
    latticeRadius c v ≤ n ↔ v ∈ latticeBox c n := by
  rw [latticeRadius, max_le_iff, mem_latticeBox]
  omega

/-- Adjacent lattice vertices have unit sup-distance. -/
theorem latticeRadius_adj {u v : LatticeVertex} (h : PD.squareLattice.Adj u v) :
    latticeRadius u v = 1 := by
  rw [squareLattice_adj_iff] at h
  rcases h with ⟨h, h2⟩ | ⟨h1, h⟩
  · rcases h with h | h <;> simp only [latticeRadius] <;> omega
  · rcases h with h | h <;> simp only [latticeRadius] <;> omega

/-- Every nearest-neighbour step increases any centred radius by at most one. -/
theorem latticeRadius_step (c : LatticeVertex) {u v : LatticeVertex}
    (h : PD.squareLattice.Adj u v) : latticeRadius c v ≤ latticeRadius c u + 1 := by
  simpa only [latticeRadius_adj h] using latticeRadius_triangle c u v

/-- Difference of global radii is bounded by the actual centred radius. -/
theorem latticeRadius_difference_le (c u v : LatticeVertex) :
    Nat.dist (latticeRadius c v) (latticeRadius c u) ≤ latticeRadius u v := by
  have hv := latticeRadius_triangle c u v
  have hu := latticeRadius_triangle c v u
  rw [latticeRadius_symm v u] at hu
  unfold Nat.dist
  omega

end PottsContinuity.BD12
