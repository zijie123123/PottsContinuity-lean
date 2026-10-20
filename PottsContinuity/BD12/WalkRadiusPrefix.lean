module

public import PottsContinuity.BD12.WalkRadiusLevel
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Stop a walk at its first visit to an integer radius level. The resulting
walk stays inside the radius ball and uses only edges of the original graph. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- A walk crossing level k has an initial traversal reaching k without ever
leaving the radius-k ball. This also applies to a configuration's open graph. -/
theorem walk_reaches_radius_inside_ball {V : Type*} {G : SimpleGraph V}
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    {x y : V} (p : G.Walk x y) (k : ℕ) (hx : r x ≤ k) (hy : k ≤ r y) :
    ∃ z, ∃ q : G.Walk x z, r z = k ∧ ∀ v ∈ q.support, r v ≤ k := by
  induction p with
  | @nil x => exact ⟨x, .nil, by omega, by simpa⟩
  | @cons x y z hxy p ih =>
    by_cases hxk : r x = k
    · exact ⟨x, .nil, hxk, by simpa⟩
    have hyk : r y ≤ k := by have h := hstep hxy; omega
    obtain ⟨u, q, hu, hq⟩ := ih hyk hy
    refine ⟨u, .cons hxy q, hu, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hx
    · exact hq v hv

/-- Radius-level reachability can be witnessed in the induced radius ball. -/
theorem reachable_radius_inside_induced_ball {V : Type*} {G : SimpleGraph V}
    (r : V → ℕ) (hstep : ∀ {x y}, G.Adj x y → r y ≤ r x + 1)
    {x y : V} (hxy : G.Reachable x y) (k : ℕ) (hx : r x ≤ k) (hy : k ≤ r y) :
    ∃ z : {v : V // r v ≤ k}, r z.val = k ∧
      (G.induce {v | r v ≤ k}).Reachable ⟨x, hx⟩ z := by
  obtain ⟨p⟩ := hxy
  obtain ⟨z, q, hz, hq⟩ := walk_reaches_radius_inside_ball r hstep p k hx hy
  have hzk : r z ≤ k := hz.le
  exact ⟨⟨z, hzk⟩, hz, ⟨q.induce {v | r v ≤ k} (by simpa only [Set.mem_ofPred_eq] using hq)⟩⟩

end PottsContinuity.BD12
