/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/PairingPathSupport.lean`.
Adaptation: namespace/import relocation only.
-/
module

public import PottsContinuity.Thm4.PairingSingleCut
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open SimpleGraph

private theorem path_support_closed_under_adj_of_two_terminal_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V} (hst : s ≠ t)
    (hs : G.degree s = 1) (ht : G.degree t = 1)
    (hother : ∀ v, v ≠ s → v ≠ t → G.degree v = 2)
    (p : G.Walk s t) (hp : p.IsPath) {v w : V}
    (hv : v ∈ p.support) (hadj : G.Adj v w) : w ∈ p.support := by
  classical
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hlen : 0 < p.length := by
    by_contra hz
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos hz
    exact hst (p.eq_of_length_eq_zero hzero)
  have hnonil : ¬p.Nil := by
    simpa [Walk.not_nil_iff_lt_length] using hlen
  have hadji : G.Adj (p.getVert i) w := hi ▸ hadj
  have hsubset (u : V) : p.toSubgraph.neighborSet u ⊆ G.neighborSet u := by
    intro z hz
    exact p.toSubgraph.adj_sub ((p.toSubgraph.mem_neighborSet u z).mp hz)
  have hstart : p.toSubgraph.neighborSet s = G.neighborSet s := by
    apply Set.eq_of_subset_of_ncard_le (hsubset s)
    rw [G.ncard_neighborSet, hs, hp.neighborSet_toSubgraph_startpoint hnonil]
    simp
  have hend : p.toSubgraph.neighborSet t = G.neighborSet t := by
    apply Set.eq_of_subset_of_ncard_le (hsubset t)
    rw [G.ncard_neighborSet, ht, hp.neighborSet_toSubgraph_endpoint hnonil]
    simp
  by_cases hi0 : i = 0
  · subst i
    have hwG : w ∈ G.neighborSet s := by simpa using hadji
    have hwP : w ∈ p.toSubgraph.neighborSet s := by rw [hstart]; exact hwG
    have hsubAdj := (p.toSubgraph.mem_neighborSet s w).mp hwP
    exact p.mem_verts_toSubgraph.mp
      (p.toSubgraph.edge_vert (p.toSubgraph.adj_symm hsubAdj))
  by_cases hilend : i = p.length
  · subst i
    have hwG : w ∈ G.neighborSet t := by simpa [Walk.getVert_length] using hadji
    have hwP : w ∈ p.toSubgraph.neighborSet t := by rw [hend]; exact hwG
    have hsubAdj := (p.toSubgraph.mem_neighborSet t w).mp hwP
    exact p.mem_verts_toSubgraph.mp
      (p.toSubgraph.edge_vert (p.toSubgraph.adj_symm hsubAdj))
  · have hiv : p.getVert i ≠ s := by
      intro heq
      have hiEq := hp.getVert_injOn (by simpa using hil) (by simp)
        (heq.trans p.getVert_zero.symm)
      exact hi0 hiEq
    have htv : p.getVert i ≠ t := by
      intro heq
      have hiEq := hp.getVert_injOn (by simpa using hil) (by simp)
        (heq.trans p.getVert_length.symm)
      exact hilend hiEq
    have hpathCard : (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 (by omega)
    have hgraphEq : p.toSubgraph.neighborSet (p.getVert i) =
        G.neighborSet (p.getVert i) := by
      apply Set.eq_of_subset_of_ncard_le (hsubset (p.getVert i))
      rw [G.ncard_neighborSet, hother (p.getVert i) hiv htv, hpathCard]
    have hwG : w ∈ G.neighborSet (p.getVert i) := hadji
    have hwP : w ∈ p.toSubgraph.neighborSet (p.getVert i) := by
      rw [hgraphEq]
      exact hwG
    have hsubAdj := (p.toSubgraph.mem_neighborSet (p.getVert i) w).mp hwP
    exact p.mem_verts_toSubgraph.mp
      (p.toSubgraph.edge_vert (p.toSubgraph.adj_symm hsubAdj))

theorem pairingGraph_path_support_closed_under_adj
    {P : Type*} [Fintype P] [DecidableEq P]
    (A B : Equiv.Perm P) (hA : Function.Involutive A)
    (hB : Function.Involutive B) (hAfree : ∀ p, A p ≠ p)
    {s t : P} (hst : s ≠ t)
    (hBfixed : ∀ p, B p = p ↔ p = s ∨ p = t)
    (p : (pairingGraph A B hA hB).Walk (s, true) (t, true))
    (hp : p.IsPath) {u v : P × Bool}
    (hu : u ∈ p.support)
    (hadj : (pairingGraph A B hA hB).Adj u v) : v ∈ p.support := by
  classical
  let G := pairingGraph A B hA hB
  have hs : G.degree (s, true) = 1 := by
    exact pairingGraph_degree_true_of_fixed A B hA hB
      ((hBfixed s).2 (Or.inl rfl))
  have ht : G.degree (t, true) = 1 := by
    exact pairingGraph_degree_true_of_fixed A B hA hB
      ((hBfixed t).2 (Or.inr rfl))
  have hother : ∀ x, x ≠ (s, true) → x ≠ (t, true) → G.degree x = 2 := by
    intro ⟨x, b⟩ hxs hxt
    cases b
    · exact pairingGraph_degree_false A B hA hB hAfree x
    · apply pairingGraph_degree_true_of_ne A B hA hB
      intro hfix
      rcases (hBfixed x).1 hfix with hx | hx
      · exact hxs (Prod.ext hx rfl)
      · exact hxt (Prod.ext hx rfl)
  have hst' : (s, true) ≠ (t, true) := by
    intro h
    exact hst (congrArg Prod.fst h)
  exact path_support_closed_under_adj_of_two_terminal_degrees G
    hst' hs ht hother p hp hu hadj

end PottsContinuity.Thm4.Medial
