-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ActualConnectionFirstHitPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Graph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-!
# First visits of simple walks to a vertex set

A simple walk that ends in a set `B` has a simple prefix, supported on the walk,
that stops at its first visit to `B` (`walk_exists_first_hit_prefix`). For the
open subgraph of an FK configuration, a vertex connected to `B` is therefore joined
to `B` by a simple open walk that meets `B` only at its endpoint
(`actualConnected_exists_first_hit_path`).
-/

/-- A simple walk ending in a set has a simple prefix whose endpoint is its
first visit to the set. Every boundary vertex on the prefix support is its
endpoint. -/
theorem walk_exists_first_hit_prefix
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Set V} {x y : V}
    (p : G.Walk x y) (hy : y ∈ B) (hp : p.IsPath) :
    ∃ z, z ∈ B ∧ ∃ q : G.Walk x z, q.IsPath ∧
      (∀ t ∈ q.support, t ∈ p.support) ∧
      (∀ t ∈ q.support, t ∈ B → t = z) := by
  induction p with
  | @nil a =>
      exact ⟨a, hy, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp, by simp⟩
  | @cons x y z hadj tail ih =>
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      by_cases hx : x ∈ B
      · exact ⟨x, hx, .nil, .nil, by simp, by simp⟩
      · have htail : tail.IsPath := by simpa using hp.tail
        obtain ⟨t, ht, q, hq, hqSub, huniq⟩ := ih hy htail
        refine ⟨t, ht, SimpleGraph.Walk.cons hadj q, ?_, ?_, ?_⟩
        · apply SimpleGraph.Walk.IsPath.cons hq
          intro hxq
          exact hnodup.1 (hqSub x hxq)
        · intro s hs
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
          rcases hs with rfl | hs
          · simp
          · exact by simp [hqSub s hs]
        · intro s hs hsB
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (hx hsB).elim
          · exact huniq s hs hsB

/-- Actual connectivity to a set yields an explicit simple open walk stopped
at its first visit to that set. The initial vertex may already be in the set,
in which case the returned walk is nil. -/
theorem actualConnected_exists_first_hit_path
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (A : Configuration G)
    {B : Set V} {x : V}
    (h : ∃ y ∈ B, ActualConnected G A x y) :
    ∃ z, z ∈ B ∧ ∃ q : (openGraph G A).Walk x z, q.IsPath ∧
      (∀ t ∈ q.support, t ∈ B → t = z) := by
  obtain ⟨y, hy, hconn⟩ := h
  obtain ⟨p⟩ := (actualConnected_iff_walk G A x y).mp hconn
  have hp : p.toPath.val.IsPath := p.toPath.property
  obtain ⟨z, hz, q, hq, _, hfirst⟩ :=
    walk_exists_first_hit_prefix p.toPath.val hy hp
  exact ⟨z, hz, q, hq, hfirst⟩

end PottsContinuity.FKC.FiniteFK
