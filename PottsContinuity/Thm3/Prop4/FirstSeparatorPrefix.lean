module

public import PottsContinuity.Thm3.Prop4.ArcPathLocality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Actual first-exit prefixes at a deterministic separator

Each retained prefix stays in the cropped domain. Every prefix edge has an
endpoint strictly before the separator, which will exclude exterior cap edges
when applied to the physical rectangle boundary.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A local edge separator gives a confined prefix to its first visited
separator vertex; each retained edge meets the domain away from the separator. -/
theorem walk_to_first_separator {V : Type*} {G : SimpleGraph V}
    (D W : Set V) (_hWD : W ⊆ D)
    (hsep : ∀ x ∈ D, ∀ y, G.Adj x y → y ∉ D → x ∈ W)
    {x y : V} (hx : x ∈ D) (hy : y ∉ D) (p : G.Walk x y) :
    ∃ z ∈ W, ∃ q : G.Walk x z,
      (∀ v ∈ q.support, v ∈ p.support) ∧ (∀ v ∈ q.support, v ∈ D) ∧
      (∀ e ∈ q.edges, ∃ v ∈ e, v ∈ D ∧ v ∉ W) := by
  classical
  induction p with
  | nil => exact False.elim (hy hx)
  | @cons x v y hxv p ih =>
    by_cases hxW : x ∈ W
    · refine ⟨x,hxW,.nil,?_,?_,?_⟩
      · intro v hv
        have heq := List.mem_singleton.mp hv
        rw [heq]
        exact SimpleGraph.Walk.start_mem_support _
      · intro v hv
        have heq := List.mem_singleton.mp hv
        exact heq ▸ hx
      · intro e he
        exact False.elim (List.not_mem_nil he)
    · have hvD : v ∈ D := by
        by_contra hv
        exact hxW (hsep x hx v hxv hv)
      obtain ⟨z,hz,q,hsub,hD,hedges⟩ := ih hvD hy
      refine ⟨z,hz,q.cons hxv,?_,?_,?_⟩
      · intro a ha
        change a ∈ x :: q.support at ha
        change a ∈ x :: p.support
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a ha)
      · intro a ha
        change a ∈ x :: q.support at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hx
        · exact hD a ha
      · intro e he
        change e ∈ s(x,v) :: q.edges at he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨x,Sym2.mem_iff'.mpr (Or.inl rfl),hx,hxW⟩
        · exact hedges e he

/-- Every escaping walk visits the separator, on its actual original support. -/
theorem walk_escape_hits_separator {V : Type*} {G : SimpleGraph V}
    (D W : Set V) (hWD : W ⊆ D)
    (hsep : ∀ x ∈ D, ∀ y, G.Adj x y → y ∉ D → x ∈ W)
    {x y : V} (hx : x ∈ D) (hy : y ∉ D) (p : G.Walk x y) :
    ∃ z ∈ p.support, z ∈ W := by
  obtain ⟨z,hz,q,hsub,_,_⟩ := walk_to_first_separator D W hWD hsep hx hy p
  exact ⟨z,hsub z q.end_mem_support,hz⟩

end PottsContinuity.Thm3.Prop4
