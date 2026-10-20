module

public import PottsContinuity.Thm3.Prop4.FirstSeparatorPrefix
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# A first-target prefix retaining the original sampled edge incidence

Stopping before the first target visit keeps every retained edge incident
to a vertex outside the target. This applies when the physical exterior is
the target and unsampled cap edges have both endpoints in that exterior.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- An actual target-reaching walk has a prefix to its first target hit,
with inherited support and each retained edge meeting the target complement. -/
theorem walk_to_first_target {V : Type*} {G : SimpleGraph V} (W : Set V)
    {x y : V} (hy : y ∈ W) (p : G.Walk x y) :
    ∃ z ∈ W, ∃ q : G.Walk x z,
      (∀ v ∈ q.support, v ∈ p.support) ∧
      (∀ e ∈ q.edges, ∃ v ∈ e, v ∉ W) := by
  classical
  induction p with
  | nil =>
    refine ⟨_,hy,.nil,?_,?_⟩
    · exact fun _ h => h
    · intro e he
      exact False.elim (List.not_mem_nil he)
  | @cons x v y hxv p ih =>
    by_cases hxW : x ∈ W
    · refine ⟨x,hxW,.nil,?_,?_⟩
      · intro v hv
        have heq := List.mem_singleton.mp hv
        rw [heq]
        exact SimpleGraph.Walk.start_mem_support _
      · intro e he
        exact False.elim (List.not_mem_nil he)
    · obtain ⟨z,hz,q,hsub,hedges⟩ := ih hy
      refine ⟨z,hz,q.cons hxv,?_,?_⟩
      · intro a ha
        change a ∈ x :: q.support at ha
        change a ∈ x :: p.support
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a ha)
      · intro e he
        change e ∈ s(x,v) :: q.edges at he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨x,Sym2.mem_iff'.mpr (Or.inl rfl),hxW⟩
        · exact hedges e he

end PottsContinuity.Thm3.Prop4
