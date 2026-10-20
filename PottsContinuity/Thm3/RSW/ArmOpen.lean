module

public import PottsContinuity.Thm3.RSW.ExteriorCircuitFinite
public import PottsContinuity.PD.RCInfinite.Cylinders
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The infinite arm event is open

Every open connection has a finite open-edge witness. Portmanteau can therefore
pass a uniform finite free arm upper bound to an infinite-volume limit without
assuming that infinite-volume clusters are finite.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Filter Topology

/-- The whole-plane actual one-arm event appearing in frozen P4. -/
def infiniteArmEvent (k : ℕ) : Set (squareLattice.edgeSet → Bool) :=
  {ω | ∃ y ∈ vertexBoundary (box k), (rcInfiniteOpenGraph ω).Reachable (0, 0) y}

/-- Actual lattice connectivity is open because a connecting walk uses finitely
many open edges. -/
theorem infinite_connection_isOpen (x y : ℤ × ℤ) :
    IsOpen {ω : squareLattice.edgeSet → Bool | (rcInfiniteOpenGraph ω).Reachable x y} := by
  have heq : {ω : squareLattice.edgeSet → Bool | (rcInfiniteOpenGraph ω).Reachable x y} =
      ⋃ n : ℕ, PD.CorrLength.connectionApprox x y n := by
    rw [← PD.CorrLength.connectionEvent_eq_iUnion_connectionApprox]
    ext ω
    exact (PD.CorrLength.connectionEvent_iff_rcInfiniteReachable x y ω).symm
  rw [heq]
  exact isOpen_iUnion (fun n => (PD.CorrLength.connectionApprox_isClopen x y n).isOpen)

/-- No finite-cluster hypothesis is used for openness of the one-arm event. -/
theorem infiniteArmEvent_isOpen (k : ℕ) : IsOpen (infiniteArmEvent k) := by
  have heq : infiniteArmEvent k = ⋃ y ∈ vertexBoundary (box k),
      {ω : squareLattice.edgeSet → Bool | (rcInfiniteOpenGraph ω).Reachable (0, 0) y} := by
    ext ω
    simp only [infiniteArmEvent, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  rw [heq]
  exact isOpen_iUnion (fun y => isOpen_iUnion (fun _ => infinite_connection_isOpen (0, 0) y))

end PottsContinuity.RSW
