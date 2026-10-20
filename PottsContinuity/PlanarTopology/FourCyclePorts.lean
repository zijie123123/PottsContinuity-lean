module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- A face label incident to an available edge of a specified four-cycle.
No edge or port is supplied when it is absent from the actual graph. -/
def fourCyclePort {V : Type*} (G : SimpleGraph V) (a b c d x : V) : Prop :=
  (G.Adj a b ∧ (x = a ∨ x = b)) ∨
  (G.Adj b c ∧ (x = b ∨ x = c)) ∨
  (G.Adj c d ∧ (x = c ∨ x = d)) ∨
  (G.Adj d a ∧ (x = d ∨ x = a))

/-- Two adjacent available edges connect every actual port of a four-cycle,
including ports belonging to either of its remaining available edges. -/
theorem fourCycle_ports_connected_of_adjacent {V : Type*} (G : SimpleGraph V)
    (a b c d : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (x y : V) (hx : fourCyclePort G a b c d x) (hy : fourCyclePort G a b c d y) :
    G.Reachable x y := by
  have hroot : ∀ z, fourCyclePort G a b c d z → G.Reachable b z := by
    intro z hz
    rcases hz with ⟨h,rfl | rfl⟩ | ⟨h,rfl | rfl⟩ | ⟨h,rfl | rfl⟩ | ⟨h,rfl | rfl⟩
    · exact hab.symm.reachable
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Reachable.refl _
    · exact hbc.reachable
    · exact hbc.reachable
    · exact hbc.reachable.trans h.reachable
    · exact hab.symm.reachable.trans h.symm.reachable
    · exact hab.symm.reachable
  exact (hroot x hx).symm.trans (hroot y hy)

/-- Cycling or reversing the four listed edges retains precisely the same
actual port predicate. -/
theorem fourCyclePort_cyclic {V : Type*} (G : SimpleGraph V) (a b c d x : V) :
    fourCyclePort G b c d a x ↔ fourCyclePort G a b c d x := by
  unfold fourCyclePort
  tauto

end PottsContinuity.PlanarTopology
