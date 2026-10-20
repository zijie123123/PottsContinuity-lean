module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push

/-- A nearest-neighbour integer-coordinate walk from inside an interval to its
exterior has an initial walk to one endpoint, wholly inside the interval. -/
theorem walk_exists_interval_exit {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (hstep : ∀ {a b}, G.Adj a b → f a - 1 ≤ f b ∧ f b ≤ f a + 1)
    (L R : ℤ) {a b : V} (p : G.Walk a b)
    (ha : L ≤ f a ∧ f a ≤ R) (hb : f b ≤ L ∨ R ≤ f b) :
    ∃ z : V, ∃ q : G.Walk a z,
      (f z = L ∨ f z = R) ∧
      (∀ w ∈ q.support, L ≤ f w ∧ f w ≤ R) ∧
      (∀ w ∈ q.support, w ∈ p.support) := by
  induction p with
  | @nil u =>
      refine ⟨u, .nil, ?_, ?_, ?_⟩
      · omega
      · intro w hw
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        subst w
        exact ha
      · exact fun _ hw => hw
  | @cons a v b hav p ih =>
      by_cases hedge : f a = L ∨ f a = R
      · refine ⟨a, .nil, hedge, ?_, ?_⟩
        · intro w hw
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          subst w
          exact ha
        · intro w hw
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          subst w
          exact SimpleGraph.Walk.start_mem_support _
      · have hnext : L ≤ f v ∧ f v ≤ R := by
          have hs := hstep hav
          omega
        obtain ⟨z,q,hz,hq,hsub⟩ := ih hnext hb
        refine ⟨z, .cons hav q, hz, ?_, ?_⟩
        · intro w hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact ha
          · exact hq w hw
        · intro w hw
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw ⊢
          rcases hw with rfl | hw
          · exact Or.inl rfl
          · exact Or.inr (hsub w hw)

end PottsContinuity.Push
