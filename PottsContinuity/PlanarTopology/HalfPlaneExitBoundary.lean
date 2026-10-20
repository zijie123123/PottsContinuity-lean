module

public import PottsContinuity.PlanarTopology.HalfPlaneExitEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite
noncomputable section

/-- Removing the sole exterior terminal from a simple representative leaves
an actual open connection from the original root to the half-plane boundary. -/
theorem exterior_terminal_walk_has_boundary_connection (ω : LatticeConfiguration)
    (u : LatticeVertex) (hu : 0 ≤ u.1) (y : ℤ)
    (p : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y))
    (hp : ∀ z ∈ p.support, 0 ≤ z.1 ∨ z = (-1,y)) :
    ω ∈ halfPlaneBoundaryEvent {u} := by
  classical
  let r := (p.toPath : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y)).reverse
  have hrpath : r.IsPath := p.toPath.property.reverse
  have hrgeom : ∀ z ∈ r.support, 0 ≤ z.1 ∨ z = (-1,y) := by
    intro z hz
    change z ∈ (p.toPath : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y)).reverse.support at hz
    have hz' : z ∈ (p.toPath : (PD.rcInfiniteOpenGraph ω).Walk u (-1,y)).support := by
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    exact hp z (p.support_toPath_subset_support hz')
  cases heq : r with
  | nil => omega
  | @cons a b c hadj q =>
    rw [heq] at hrpath hrgeom
    have hnot : (-1,y) ∉ q.support := (List.nodup_cons.mp hrpath.support_nodup).1
    have hqH : ∀ z ∈ q.support, 0 ≤ z.1 := by
      intro z hz
      rcases hrgeom z (List.mem_cons.mpr (Or.inr hz)) with h | h
      · exact h
      · exact (hnot (h ▸ hz)).elim
    have hbH := hqH b q.start_mem_support
    have hstep := (squareLattice_adj_iff (-1,y) b).mp (rcOpenGraph_le_squareLattice ω hadj)
    have hb0 : b.1 = 0 := by dsimp at hstep; rcases hstep with h | h <;> omega
    refine ⟨⟨u,hu⟩,Set.mem_singleton u,⟨b,hbH⟩,hb0,?_⟩
    have hrevH : ∀ z ∈ q.reverse.support, z ∈ ({z : LatticeVertex | 0 ≤ z.1} : Set LatticeVertex) := by
      intro z hz
      apply hqH z
      simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    exact ⟨q.reverse.induce _ hrevH⟩

end
end PottsContinuity.PlanarTopology
