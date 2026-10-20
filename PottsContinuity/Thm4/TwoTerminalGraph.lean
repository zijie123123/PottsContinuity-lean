/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/TwoTerminalGraph.lean`.
Adaptation: namespace relocation only.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# The unique open path in a finite two-terminal graph

A finite simple graph with two distinct vertices of degree one and every other
vertex of degree two has exactly one simple walk between its two terminals.
Other components may be cycles; global connectedness and acyclicity are not
assumed. This is a combinatorial lemma: a concrete medial model must separately
prove these degree conditions for its actual graph.
-/

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With degree at most two, there is at most one neighbor other than a given neighbor. -/
private theorem neighbor_eq_of_degree_le_two {u r v w : V}
    (hdeg : G.degree u ≤ 2) (hr : G.Adj u r) (hv : G.Adj u v) (hw : G.Adj u w)
    (hrv : r ≠ v) (hrw : r ≠ w) : v = w := by
  classical
  by_contra hvw
  have hsub : ({r, v, w} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simpa only [mem_neighborFinset] using ‹G.Adj u x›
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
    hrv, hrw, hvw, or_self, not_false_eq_true, Finset.card_singleton] at hcard
  change 3 ≤ G.degree u at hcard
  omega

/-- Two simple continuations cannot branch after the same incoming edge. -/
private theorem isPath_eq_of_previous (hdeg : ∀ u, G.degree u ≤ 2)
    {u v : V} (p : G.Walk u v) :
    ∀ {r : V} (q : G.Walk u v), G.Adj r u → p.IsPath → q.IsPath →
      r ∉ p.support → r ∉ q.support → p = q := by
  induction p with
  | nil =>
    intro r q _ _ hq _ _
    exact (Walk.isPath_iff_nil.mp hq).eq_nil.symm
  | @cons u w v huw p ih =>
    intro r q hru hp hq hrp hrq
    cases q with
    | nil => exact False.elim ((Walk.not_nil_cons) (Walk.isPath_iff_nil.mp hp))
    | @cons _ z _ huz q =>
      have hrw : r ≠ w := by
        intro h
        apply hrp
        subst r
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr p.start_mem_support
      have hrz : r ≠ z := by
        intro h
        apply hrq
        subst r
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr q.start_mem_support
      have hwz := neighbor_eq_of_degree_le_two G (hdeg u) hru.symm huw huz hrw hrz
      subst z
      obtain ⟨hp', hup⟩ := (Walk.cons_isPath_iff _ _).mp hp
      obtain ⟨hq', huq⟩ := (Walk.cons_isPath_iff _ _).mp hq
      have hpq := ih q huw hp' hq' hup huq
      cases hpq
      rfl

/-- In a graph of maximum degree two, every simple walk from a degree-one vertex
is uniquely determined by its endpoint. -/
theorem isPath_eq_of_degree_le_two {s t : V} (hdeg : ∀ u, G.degree u ≤ 2)
    (hs : G.degree s = 1) (p q : G.Walk s t) (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  cases p with
  | nil => exact (Walk.isPath_iff_nil.mp hq).eq_nil.symm
  | @cons _ u _ hsu p =>
    cases q with
    | nil => exact False.elim (Walk.not_nil_cons (Walk.isPath_iff_nil.mp hp))
    | @cons _ v _ hsv q =>
      obtain ⟨w, hw, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hs
      have huv : u = v := (huniq u hsu).trans (huniq v hsv).symm
      subst v
      obtain ⟨hp', hsp⟩ := (Walk.cons_isPath_iff _ _).mp hp
      obtain ⟨hq', hsq⟩ := (Walk.cons_isPath_iff _ _).mp hq
      have hpq := isPath_eq_of_previous G hdeg p q hsu hp' hq' hsp hsq
      cases hpq
      rfl

/-- The degree conditions force the two terminals into the same component,
while permitting closed components elsewhere. -/
theorem reachable_of_two_terminal_degrees {s t : V} (hst : s ≠ t)
    (hs : G.degree s = 1) (ht : G.degree t = 1)
    (hother : ∀ v, v ≠ s → v ≠ t → G.degree v = 2) : G.Reachable s t := by
  classical
  by_cases hadj : G.Adj s t
  · exact hadj.reachable
  let H := G ⊔ SimpleGraph.edge s t
  have hns : H.neighborSet s = insert t (G.neighborSet s) := by
    ext v
    simp only [H, mem_neighborSet, sup_adj, edge_adj, Set.mem_insert_iff]
    aesop
  have hnt : H.neighborSet t = insert s (G.neighborSet t) := by
    ext v
    simp only [H, mem_neighborSet, sup_adj, edge_adj, Set.mem_insert_iff]
    aesop
  have hnother (v : V) (hvs : v ≠ s) (hvt : v ≠ t) :
      H.neighborSet v = G.neighborSet v := by
    ext w
    simp only [H, mem_neighborSet, sup_adj, edge_adj, hvs, hvt, false_and,
      or_false]
  have hcycles : H.IsCycles := by
    intro v _
    by_cases hvs : v = s
    · subst v
      have hnot : t ∉ G.neighborSet s := hadj
      rw [hns, Set.ncard_insert_of_notMem hnot, G.ncard_neighborSet, hs]
    by_cases hvt : v = t
    · subst v
      have hnot : s ∉ G.neighborSet t := fun h => hadj h.symm
      rw [hnt, Set.ncard_insert_of_notMem hnot, G.ncard_neighborSet, ht]
    rw [hnother v hvs hvt, G.ncard_neighborSet, hother v hvs hvt]
  have hedge : H.Adj s t := by
    exact Or.inr ((SimpleGraph.edge_adj s t s t).mpr ⟨Or.inl ⟨rfl, rfl⟩, hst⟩)
  have hdelete : H.deleteEdges {s(s, t)} = G := by
    simp only [H, deleteEdges_sup, SimpleGraph.edge, deleteEdges_fromEdgeSet,
      Set.sdiff_self, fromEdgeSet_empty, sup_bot_eq]
    apply deleteEdges_eq_self.mpr
    simpa only [Set.disjoint_singleton_right, mem_edgeSet] using hadj
  rw [← hdelete]
  exact hcycles.reachable_deleteEdges hedge

/-- Exactly one simple walk connects the two distinct degree-one terminals of a
finite graph whose remaining vertices have degree two. -/
theorem existsUnique_isPath_of_two_terminal_degrees {s t : V} (hst : s ≠ t)
    (hs : G.degree s = 1) (ht : G.degree t = 1)
    (hother : ∀ v, v ≠ s → v ≠ t → G.degree v = 2) :
    ∃! p : G.Walk s t, p.IsPath := by
  obtain ⟨p, hp⟩ := (reachable_of_two_terminal_degrees G hst hs ht hother).exists_isPath
  have hdeg (v : V) : G.degree v ≤ 2 := by
    by_cases hvs : v = s
    · subst v
      omega
    by_cases hvt : v = t
    · subst v
      omega
    exact (hother v hvs hvt).le
  exact ⟨p, hp, fun q hq => isPath_eq_of_degree_le_two G hdeg hs q p hq hp⟩

end PottsContinuity.Thm4.Medial
