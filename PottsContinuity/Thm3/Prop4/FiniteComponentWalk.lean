module

public import PottsContinuity.Thm3.Prop4.RecordedFrontierTraceArms

/-!
# Whole finite component traces with actual walk witnesses

Repeated visits let an original u-v walk cover the whole connected component.
Existence of the walk is separate from the canonical finite trace and makes
no choice of a particular path in that trace definition.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A finite collection of vertices connected to u can all be visited by one
actual u-v walk whenever v is connected to u. Repeated visits are retained. -/
theorem exists_walk_covering_finite_connected_set {V : Type*} {G : SimpleGraph V}
    {u v : V} (S : Finset V) (hS : ∀ x ∈ S, G.Reachable u x)
    (huv : G.Reachable u v) :
    ∃ p : G.Walk u v, ∀ x ∈ S, x ∈ p.support := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨p⟩ := huv
    exact ⟨p,by simp⟩
  | @insert x S hx ih =>
    obtain ⟨p,hp⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    obtain ⟨q⟩ := hS x (Finset.mem_insert_self x S)
    refine ⟨q.append (q.reverse.append p),?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl q.end_mem_support
    · rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inr (Or.inr (hp y hy))

/-- The whole component of u in a finite graph is exactly the support of an
actual walk from u to any v in that component. -/
theorem exists_walk_support_eq_finite_component {V : Type*} [fintypeV : Fintype V]
    (G : SimpleGraph V) (u v : V) (huv : G.Reachable u v) :
    ∃ p : G.Walk u v, ∀ x : V, x ∈ p.support ↔ G.Reachable u x := by
  classical
  let S := Finset.univ.filter fun x => G.Reachable u x
  obtain ⟨p,hp⟩ := exists_walk_covering_finite_connected_set S
    (fun x hx => (Finset.mem_filter.mp hx).2) huv
  refine ⟨p,fun x => ⟨?_,?_⟩⟩
  · intro hx
    exact ⟨p.takeUntil x hx⟩
  · intro hx
    exact hp x (Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩)

end PottsContinuity.Thm3.Prop4
