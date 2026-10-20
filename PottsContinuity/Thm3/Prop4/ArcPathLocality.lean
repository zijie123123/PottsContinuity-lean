module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Locality of actual connection-plus-no-escape events

A connection to the arc can be stopped before leaving the finite target.
A path violating no-escape can be stopped at its first exit, using only edges
incident to that target. These are deterministic statements on arbitrary graphs.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
variable {V : Type*} {G : SimpleGraph V}

/-- A root-to-arc connection under no-escape has a witness entirely in the target. -/
theorem walk_to_arc_confined_of_no_escape (D W : Set V) (hWD : W ⊆ D)
    {x y : V} (hx : x ∈ D) (hy : y ∈ W) (p : G.Walk x y)
    (hno : ∀ v : V, v ∉ D → ∀ q : G.Walk x v, ∃ z ∈ q.support, z ∈ W) :
    ∃ z ∈ W, ∃ q : G.Walk x z, ∀ v ∈ q.support, v ∈ D := by
  classical
  have hwalk : ∀ {u v : V} (q : G.Walk u v), u ∈ D → v ∈ W →
      (∀ w : V, w ∉ D → ∀ r : G.Walk u w, ∃ z ∈ r.support, z ∈ W) →
      ∃ z ∈ W, ∃ r : G.Walk u z, ∀ w ∈ r.support, w ∈ D := by
    intro u v q
    induction q with
    | nil =>
      intro hu hv _
      refine ⟨_,hv,.nil,?_⟩
      intro a ha
      rcases List.mem_singleton.mp ha with rfl
      exact hu
    | @cons u v w huv q ih =>
      intro hu hw hno
      by_cases huW : u ∈ W
      · refine ⟨u,huW,.nil,?_⟩
        intro a ha
        rcases List.mem_singleton.mp ha with rfl
        exact hu
      have hv : v ∈ D := by
        by_contra hv
        obtain ⟨z,hz,hzW⟩ := hno v hv (.cons huv .nil)
        change z ∈ [u,v] at hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl
        · exact huW hzW
        · exact hv (hWD hzW)
      have hnoV : ∀ z : V, z ∉ D → ∀ r : G.Walk v z, ∃ a ∈ r.support, a ∈ W := by
        intro z hz r
        obtain ⟨a,ha,haW⟩ := hno z hz (.cons huv r)
        change a ∈ u :: r.support at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact False.elim (huW haW)
        · exact ⟨a,ha,haW⟩
      obtain ⟨z,hz,r,hr⟩ := ih hv hw hnoV
      refine ⟨z,hz,.cons huv r,?_⟩
      intro a ha
      change a ∈ u :: r.support at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hu
      · exact hr a ha
  exact hwalk p hx hy hno

/-- A violating path has a first-exit prefix using only edges incident to the target. -/
theorem first_exit_avoiding_walk (D W : Set V) {x y : V} (hx : x ∈ D) (hy : y ∉ D)
    (p : G.Walk x y) (hp : ∀ z ∈ p.support, z ∉ W) :
    ∃ z ∉ D, ∃ q : G.Walk x z,
      (∀ e ∈ q.edges, ∃ v ∈ e, v ∈ D) ∧ (∀ v ∈ q.support, v ∉ W) := by
  have hwalk : ∀ {u v : V} (q : G.Walk u v), u ∈ D → v ∉ D →
      (∀ z ∈ q.support, z ∉ W) →
      ∃ z ∉ D, ∃ r : G.Walk u z,
        (∀ e ∈ r.edges, ∃ a ∈ e, a ∈ D) ∧ (∀ a ∈ r.support, a ∉ W) := by
    intro u v q
    induction q with
    | nil => exact fun hu hv _ => False.elim (hv hu)
    | @cons u v w huv q ih =>
      intro hu hw havoid
      classical
      have huW : u ∉ W := havoid u (by change u ∈ u :: q.support; exact List.mem_cons_self)
      by_cases hv : v ∈ D
      · have htail : ∀ z ∈ q.support, z ∉ W := fun z hz => havoid z (List.mem_cons_of_mem _ hz)
        obtain ⟨z,hz,r,hedges,hsupport⟩ := ih hv hw htail
        refine ⟨z,hz,.cons huv r,?_,?_⟩
        · intro e he
          change e ∈ s(u,v) :: r.edges at he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨u,Sym2.mem_iff'.mpr (Or.inl rfl),hu⟩
          · exact hedges e he
        · intro a ha
          change a ∈ u :: r.support at ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact huW
          · exact hsupport a ha
      · refine ⟨v,hv,.cons huv .nil,?_,?_⟩
        · intro e he
          change e ∈ [s(u,v)] at he
          have heq := List.mem_singleton.mp he
          rw [heq]
          exact ⟨u,Sym2.mem_iff'.mpr (Or.inl rfl),hu⟩
        · intro a ha
          change a ∈ [u,v] at ha
          simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with ha | ha
          · rw [ha]
            exact huW
          · rw [ha]
            exact havoid _ (List.mem_cons_of_mem _ q.start_mem_support)
  exact hwalk p hx hy hp

end PottsContinuity.Thm3.Prop4
