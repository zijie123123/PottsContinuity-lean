module

public import PottsContinuity.PD.FK.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK

/-- A horizontal lattice interval has a walk visiting only that interval. -/
theorem horizontal_interval_walk (a y : ℤ) (n : ℕ) :
    ∃ p : squareLattice.Walk (a,y) (a + (n : ℤ),y),
      ∀ z ∈ p.support, a ≤ z.1 ∧ z.1 ≤ a + (n : ℤ) ∧ z.2 = y := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    exact ⟨.nil, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    have hstep : squareLattice.Adj (a + (n : ℤ), y) (a + ((n+1 : ℕ) : ℤ), y) := by
      simp [squareLattice_adj_iff, Nat.cast_add, add_assoc]
    refine ⟨p.concat hstep, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_concat] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have h := hp z hz
      exact ⟨h.1, by omega, h.2.2⟩
    · have hz := List.mem_singleton.mp hz
      subst z
      exact ⟨by dsimp; omega, le_rfl, rfl⟩

/-- Horizontal connections between arbitrary ordered integer coordinates. -/
theorem horizontal_walk_between (a b y : ℤ) :
    ∃ p : squareLattice.Walk (a,y) (b,y),
      ∀ z ∈ p.support, min a b ≤ z.1 ∧ z.1 ≤ max a b ∧ z.2 = y := by
  by_cases hab : a ≤ b
  · have h := horizontal_interval_walk a y (b-a).toNat
    have he : a + (((b-a).toNat : ℕ) : ℤ) = b := by omega
    rw [he] at h
    simpa only [min_eq_left hab, max_eq_right hab] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have h := horizontal_interval_walk b y (a-b).toNat
    have he : b + (((a-b).toNat : ℕ) : ℤ) = a := by omega
    rw [he] at h
    obtain ⟨p, hp⟩ := h
    refine ⟨p.reverse, ?_⟩
    intro z hz
    have hz' : z ∈ p.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    simpa only [min_eq_right hba, max_eq_left hba] using hp z hz'

end PottsContinuity.PlanarTopology
