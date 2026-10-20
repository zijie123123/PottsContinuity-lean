module

public import PottsContinuity.BD12.LatticeRadius
public import PottsContinuity.PD.RCInfinite.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Nat.Dist

/-! The exact metric data on every finite closed lattice box, including its
centre and isolated vertices. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite

/-- Actual centre vertex of a closed lattice box. -/
def radiusBoxCenter (c : LatticeVertex) (n : ℕ) : (latticeBox c n : Set LatticeVertex) :=
  ⟨c, center_mem_latticeBox c n⟩

abbrev boxGlobalRadius (c : LatticeVertex) (n : ℕ)
    (v : (latticeBox c n : Set LatticeVertex)) : ℕ := latticeRadius c v.val

abbrev boxCentredRadius (c : LatticeVertex) (n : ℕ)
    (u v : (latticeBox c n : Set LatticeVertex)) : ℕ := latticeRadius u.val v.val

@[simp] theorem boxGlobalRadius_center (c : LatticeVertex) (n : ℕ) :
    boxGlobalRadius c n (radiusBoxCenter c n) = 0 := latticeRadius_self c

theorem boxGlobalRadius_le (c : LatticeVertex) (n : ℕ)
    (v : (latticeBox c n : Set LatticeVertex)) : boxGlobalRadius c n v ≤ n :=
  (latticeRadius_le_iff_mem_box c v.val n).mpr v.property

theorem boxGlobalRadius_step (c : LatticeVertex) (n : ℕ)
    {u v : (latticeBox c n : Set LatticeVertex)}
    (h : (finiteLatticeGraph (latticeBox c n)).Adj u v) :
    boxGlobalRadius c n v ≤ boxGlobalRadius c n u + 1 := latticeRadius_step c h

@[simp] theorem boxCentredRadius_self (c : LatticeVertex) (n : ℕ)
    (u : (latticeBox c n : Set LatticeVertex)) : boxCentredRadius c n u u = 0 :=
  latticeRadius_self u.val

theorem boxCentredRadius_step (c : LatticeVertex) (n : ℕ)
    (u : (latticeBox c n : Set LatticeVertex))
    {v w : (latticeBox c n : Set LatticeVertex)}
    (h : (finiteLatticeGraph (latticeBox c n)).Adj v w) :
    boxCentredRadius c n u w ≤ boxCentredRadius c n u v + 1 := latticeRadius_step u.val h

theorem boxRadius_difference_le (c : LatticeVertex) (n : ℕ)
    (u v : (latticeBox c n : Set LatticeVertex)) :
    Nat.dist (boxGlobalRadius c n v) (boxGlobalRadius c n u) ≤ boxCentredRadius c n u v :=
  latticeRadius_difference_le c u.val v.val

end PottsContinuity.BD12
