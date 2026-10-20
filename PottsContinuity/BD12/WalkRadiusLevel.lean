module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

/-! Integer-radius intermediate values along graph walks. This is a graph
metric fact, with no planar separation assumption or percolation input. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- A graph walk starting at radius at most k and ending at radius at least k
visits radius exactly k whenever each upward edge changes radius by at most one. -/
theorem walk_visits_radius_level {V : Type*} {G : SimpleGraph V}
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    {x y : V} (p : G.Walk x y) (k : ℕ) (hx : r x ≤ k) (hy : k ≤ r y) :
    ∃ z, z ∈ p.support ∧ r z = k := by
  induction p with
  | @nil x => exact ⟨x, by simp, by omega⟩
  | @cons x z y hxz p ih =>
    by_cases hxeq : r x = k
    · exact ⟨x, by simp, hxeq⟩
    have hz : r z ≤ k := by have h := hstep hxz; omega
    obtain ⟨u, hu, hru⟩ := ih hz hy
    exact ⟨u, by simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using Or.inr hu, hru⟩

/-- The exact finite shell of radius k for a supplied integer radius function. -/
def finiteRadiusShell {V : Type*} [Fintype V] (r : V → ℕ) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => r v = k)

@[simp] theorem mem_finiteRadiusShell {V : Type*} [Fintype V] (r : V → ℕ) (k : ℕ) (v : V) :
    v ∈ finiteRadiusShell r k ↔ r v = k := by simp [finiteRadiusShell]

/-- Every walk crossing a radius level hits the literal finite shell. -/
theorem walk_visits_finiteRadiusShell {V : Type*} [Fintype V] {G : SimpleGraph V}
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    {o b : V} (p : G.Walk o b) (k : ℕ) (ho : r o ≤ k) (hb : k ≤ r b) :
    ∃ s, s ∈ p.support ∧ s ∈ finiteRadiusShell r k := by
  obtain ⟨s, hs, hrs⟩ := walk_visits_radius_level r hstep p k ho hb
  exact ⟨s, hs, (mem_finiteRadiusShell r k s).mpr hrs⟩

end PottsContinuity.BD12
