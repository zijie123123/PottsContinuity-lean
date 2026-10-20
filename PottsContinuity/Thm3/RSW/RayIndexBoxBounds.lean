module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # Ray indices outside a translated support box -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality

/-- A closed walk supported in a translated box has zero index outside that box. -/
theorem closedWalk_rayIndex_zero_outside_box
    (c : LatticeVertex) (r : ℕ) {z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk z z)
    (hp : ∀ v ∈ p.support, v ∈ latticeBox c r)
    (x : LatticeVertex) (hx : x ∉ latticeBox c r) :
    rayIndex x p = 0 := by
  have hb (v : LatticeVertex) (hv : v ∈ p.support) :=
    (mem_latticeBox c v r).mp (hp v hv)
  have hx' : x.1 < c.1 - (r : ℤ) ∨ c.1 + (r : ℤ) < x.1 ∨
      x.2 < c.2 - (r : ℤ) ∨ c.2 + (r : ℤ) < x.2 := by
    rw [mem_latticeBox] at hx
    omega
  rcases hx' with hl | hr | hb' | ht
  · rw [rayIndex_left_telescope x p (fun v hv => by have := hb v hv; omega)]
    omega
  · exact rayIndex_zero_of_right x p (fun v hv => by have := hb v hv; omega)
  · apply rayIndex_zero_of_level x p 0
    intro v hv
    have := hb v hv
    exact ite_eq_right (by omega)
  · apply rayIndex_zero_of_level x p 1
    intro v hv
    have := hb v hv
    exact ite_eq_left (by omega)

/-- Extracting a nonempty cycle using only old edges preserves support bounds. -/
theorem cycle_support_subset_of_edges_subset
    {X : Type*} {G : SimpleGraph X} {a b : X}
    (p : G.Walk a a) (q : G.Walk b b) (hq : q.IsCycle)
    (hedges : q.edges ⊆ p.edges) : q.support ⊆ p.support := by
  intro v hv
  obtain ⟨e,he,hv'⟩ :=
    (q.mem_support_iff_exists_mem_edges_of_not_nil hq.not_nil).mp hv
  exact p.mem_support_of_mem_edges (hedges he) hv'

end PottsContinuity.RSW
