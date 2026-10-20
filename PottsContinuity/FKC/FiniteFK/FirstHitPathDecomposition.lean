-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FirstHitPathDecomposition.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- Split a simple walk at its first visit to `B`. The retained prefix and
suffix concatenate to the original walk, so prefix edges are preserved. -/
theorem walk_exists_first_hit_decomposition
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Set V} {x y : V}
    (p : G.Walk x y) (hy : y ∈ B) (hp : p.IsPath) :
    ∃ z, z ∈ B ∧ ∃ q : G.Walk x z, ∃ r : G.Walk z y,
      q.IsPath ∧ q.append r = p ∧
      (∀ t, t ∈ q.support → t ∈ B → t = z) ∧
      (∀ t, t ∈ q.support → t ∈ p.support) ∧
      (∀ e, e ∈ q.edges → e ∈ p.edges) := by
  induction p with
  | @nil a =>
      exact ⟨a, hy, .nil, .nil, .nil, rfl, by simp, by simp, by simp⟩
  | @cons a b c hab tail ih =>
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      by_cases ha : a ∈ B
      · refine ⟨a, ha, .nil, SimpleGraph.Walk.cons hab tail, .nil, ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro t ht
          simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inl ht
        · simp
      · have htail : tail.IsPath := by simpa using hp.tail
        obtain ⟨z, hz, q, r, hq, hsplit, hfirst, hqSupport, hqEdges⟩ := ih hy htail
        let q' : G.Walk a z := SimpleGraph.Walk.cons hab q
        have hqInTail : ∀ t, t ∈ q.support → t ∈ tail.support := by
          intro t ht
          have hs := SimpleGraph.Walk.support_subset_support_append_left q r
          rw [hsplit] at hs
          exact hs ht
        have hsplit' : q'.append r = SimpleGraph.Walk.cons hab tail := by
          simp [q', hsplit]
        refine ⟨z, hz, q', r, ?_, hsplit', ?_, ?_, ?_⟩
        · apply SimpleGraph.Walk.IsPath.cons hq
          intro hmem
          exact hnodup.1 (hqInTail a hmem)
        · intro t ht htB
          simp only [q', SimpleGraph.Walk.support_cons, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact (ha htB).elim
          · exact hfirst t ht htB
        · intro t ht
          simp only [q', SimpleGraph.Walk.support_cons, List.mem_cons] at ht ⊢
          rcases ht with rfl | ht
          · exact Or.inl rfl
          · exact Or.inr (hqSupport t ht)
        · intro e he
          have hEdges : q'.edges ++ r.edges = (SimpleGraph.Walk.cons hab tail).edges := by
            have := congrArg SimpleGraph.Walk.edges hsplit'
            simpa [SimpleGraph.Walk.edges_append] using this
          rw [← hEdges]
          simp only [List.mem_append]
          exact Or.inl (by simpa [q'] using he)

end PottsContinuity.FKC.FiniteFK
