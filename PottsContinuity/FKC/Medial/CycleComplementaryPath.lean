-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/CycleComplementaryPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.CycleDegreeTwoPropagation
public import PottsContinuity.FKC.Medial.FiniteEvenSubgraphOfCycle
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem isPath_eq_of_edge_subset
    {V : Type*} {G : SimpleGraph V} {u v : V}
    {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hsubset : ∀ e, e ∈ q.edges → e ∈ p.edges) : p = q := by
  induction q with
  | nil =>
      have hpNil : p.Nil := hp.nil_iff_eq.mpr rfl
      cases p with
      | nil => rfl
      | cons h t => simp at hpNil
  | @cons x y z hxy tail ih =>
      have hfirst : s(x,y) ∈ p.edges := hsubset _ (by simp)
      have hysnd : p.snd = y := (hp.eq_snd_of_mem_edges hfirst).symm
      cases p with
      | nil => simp at hfirst
      | @cons x' y' z' hxy' ptail =>
          have hxyEq : y' = y := by simpa using hysnd
          subst y'
          have htailP := (Walk.cons_isPath_iff hxy' ptail).mp hp |>.1
          have htailQ := (Walk.cons_isPath_iff hxy tail).mp hq |>.1
          have htailSub : ∀ e, e ∈ tail.edges → e ∈ ptail.edges := by
            intro e he
            have heP := hsubset e (by simp [he])
            simp only [Walk.edges_cons, List.mem_cons] at heP
            rcases heP with heq | heP
            · subst e
              have hqNodup := hq.edges_nodup
              simp only [Walk.edges_cons, List.nodup_cons] at hqNodup
              exact (hqNodup.1 he).elim
            · exact heP
          have htailEq := ih (p := ptail) htailP htailQ htailSub
          simp [htailEq]

private theorem spanningCycle_le_of_edge_subset
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u u) (q : G.Walk v v)
    (hEdges : ∀ e, e ∈ q.edges → e ∈ p.edges) :
    q.toSubgraph.spanningCoe ≤ p.toSubgraph.spanningCoe := by
  rw [SimpleGraph.le_iff_adj]
  intro x y hxy
  change q.toSubgraph.Adj x y at hxy
  have hqEdge : s(x,y) ∈ q.edges := q.adj_toSubgraph_iff_mem_edges.mp hxy
  have hpEdge := hEdges _ hqEdge
  change p.toSubgraph.Adj x y
  exact p.adj_toSubgraph_iff_mem_edges.mpr hpEdge

private theorem cycle_subgraph_eq_of_edge_subset
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u u) (hp : p.IsCycle)
    (q : G.Walk v v) (hq : q.IsCycle)
    (hEdges : ∀ e, e ∈ q.edges → e ∈ p.edges) :
    q.toSubgraph.spanningCoe = p.toSubgraph.spanningCoe := by
  classical
  let D := q.toSubgraph.spanningCoe
  let C := p.toSubgraph.spanningCoe
  have hDC : D ≤ C := spanningCycle_le_of_edge_subset p q hEdges
  have hsubgraph : q.toSubgraph ≤ p.toSubgraph := by
    apply (q.toSubgraph_le_iff hq.not_nil).2
    intro e he
    have heWalk : e ∈ q.edges := by
      exact he
    exact p.mem_edges_toSubgraph.mpr (hEdges e heWalk)
  have hDneighbor (x : V) (hx : x ∈ q.support) :
      C.neighborSet x = D.neighborSet x := by
    have hxQ : x ∈ q.toSubgraph.verts := q.mem_verts_toSubgraph.mpr hx
    have hxP : x ∈ p.toSubgraph.verts := Subgraph.verts_mono hsubgraph hxQ
    have hxP : x ∈ p.support := by
      exact p.mem_verts_toSubgraph.mp hxP
    have hdeg : (C.neighborSet x).ncard = 2 := by
      change (p.toSubgraph.neighborSet x).ncard = 2
      exact hp.ncard_neighborSet_toSubgraph_eq_two hxP
    exact cycle_neighborSet_eq_of_degree_two q hq hDC hx hdeg
  have hstartC : v ∈ p.support := by
    have hqNotNil := hq.not_nil
    have hqAdj : q.toSubgraph.Adj v q.snd := q.toSubgraph_adj_snd hqNotNil
    have hpAdj := hsubgraph.2 hqAdj
    exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hpAdj)
  have hprop : ∀ {x y : p.toSubgraph.verts}
      (w : p.toSubgraph.coe.Walk x y),
      x.1 ∈ q.support → y.1 ∈ q.support := by
    intro x y w
    induction w with
    | nil => exact fun hx => hx
    | @cons x y z hadj tail ih =>
        intro hx
        have hEq := hDneighbor x.1 hx
        have hyC : y.1 ∈ C.neighborSet x.1 :=
          (C.mem_neighborSet x.1 y.1).mpr hadj
        have hyD : y.1 ∈ D.neighborSet x.1 := by simpa [hEq] using hyC
        have hxyD : D.Adj x.1 y.1 := (D.mem_neighborSet x.1 y.1).mp hyD
        have hyV : y.1 ∈ q.toSubgraph.verts := q.toSubgraph.edge_vert hxyD.symm
        have hySupport : y.1 ∈ q.support := q.mem_verts_toSubgraph.mp hyV
        exact ih hySupport
  have hfull : ∀ x : V, x ∈ p.support → x ∈ q.support := by
    intro x hx
    let xq : q.toSubgraph.verts := ⟨v, q.mem_verts_toSubgraph.mpr q.start_mem_support⟩
    let xp : p.toSubgraph.verts := ⟨v, p.mem_verts_toSubgraph.mpr hstartC⟩
    let yp : p.toSubgraph.verts := ⟨x, p.mem_verts_toSubgraph.mpr hx⟩
    have hreach : p.toSubgraph.coe.Reachable xp yp := p.toSubgraph_connected xp yp
    rcases hreach with ⟨w⟩
    exact hprop w q.start_mem_support
  apply le_antisymm hDC
  intro x y hxy
  have hxV : x ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hxy
  have hxSupport := p.mem_verts_toSubgraph.mp hxV
  have hxQ := hfull x hxSupport
  have hEq := hDneighbor x hxQ
  have hyC : y ∈ C.neighborSet x := (C.mem_neighborSet x y).mpr hxy
  have hyD : y ∈ D.neighborSet x := by simpa [hEq] using hyC
  exact (D.mem_neighborSet x y).mp hyD

/-- A simple path in a simple cycle is one of its two arcs. -/
theorem exists_complementary_path
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (c : G.Walk a a) (hc : c.IsCycle)
    (r : G.Walk a b) (hr : r.IsPath)
    (hrc : ∀ e, e ∈ r.edges → e ∈ c.edges) :
    ∃ s : G.Walk b a, s.IsPath ∧
      List.Disjoint r.edges s.edges ∧
      (∀ e, e ∈ c.edges → e ∈ r.edges ∨ e ∈ s.edges) ∧
      (∀ e, e ∈ r.edges ∨ e ∈ s.edges → e ∈ c.edges) ∧
      (r.append s).IsCycle := by
  classical
  have hrne : ¬ r.Nil := by
    intro hnil
    exact hab (Walk.Nil.eq hnil)
  have hbR : b ∈ r.support := r.end_mem_support
  have hbC : b ∈ c.support := by
    obtain ⟨e, he, hbe⟩ := (r.mem_support_iff_exists_mem_edges_of_not_nil hrne).mp hbR
    have hce := hrc e he
    exact (c.mem_support_iff_exists_mem_edges).mpr (Or.inr ⟨e, hce, hbe⟩)
  let arc : G.Walk a b := c.takeUntil b hbC
  let back : G.Walk b a := c.dropUntil b hbC
  have harc : arc.IsPath := hc.isPath_takeUntil hbC
  have hsplit : arc.append back = c := c.take_spec hbC
  have hback : back.IsPath := by
    have hcycle : (arc.append back).IsCycle := by rw [hsplit]; exact hc
    apply hcycle.isPath_of_append_right (p := arc) (q := back)
    intro hnil
    exact hab (Walk.Nil.eq (p := arc) hnil)
  by_cases hEq : r = arc
  · refine ⟨back, ?_, ?_, ?_, ?_, ?_⟩
    · exact hback
    · simpa [hEq, arc, back] using hc.isTrail.disjoint_edges_takeUntil_dropUntil hbC
    · intro e he
      have hmem : e ∈ arc.edges ∨ e ∈ back.edges := by
        have hwalk := congrArg Walk.edges hsplit
        simp only [Walk.edges_append] at hwalk
        rw [← hwalk] at he
        exact List.mem_append.mp he
      simpa [hEq] using hmem
    · intro e he
      rcases he with he | he
      · exact hrc e he
      · have hwalk := congrArg Walk.edges hsplit
        simp only [Walk.edges_append] at hwalk
        rw [← hwalk]
        exact List.mem_append_right _ he
    · simpa [hEq, hsplit] using hc
  · obtain ⟨u, v, p', q', hpSub, hqSub, hd⟩ := hr.exists_isCycle_of_ne harc hEq
    have hde : ∀ e, e ∈ (p'.append q'.reverse).edges → e ∈ c.edges := by
      intro e he
      simp only [Walk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hrc e (hpSub.edges_subset he)
      · have hq : e ∈ q'.edges := by simpa using he
        have ha : e ∈ arc.edges := hqSub.edges_subset hq
        exact c.edges_takeUntil_subset_edges hbC ha
    have hcycleEq := cycle_subgraph_eq_of_edge_subset c hc (p'.append q'.reverse) hd hde
    have hbackSub : ∀ e, e ∈ back.edges → e ∈ r.edges := by
      intro e he
      have hcEdge : e ∈ c.edges := by
        have hwalk := congrArg Walk.edges hsplit
        simp only [Walk.edges_append] at hwalk
        rw [← hwalk]
        exact List.mem_append_right _ he
      have hdEdge : e ∈ (p'.append q'.reverse).edges := by
        have hdSet : e ∈ (p'.append q'.reverse).toSubgraph.edgeSet := by
          rw [← Subgraph.edgeSet_spanningCoe, hcycleEq, Subgraph.edgeSet_spanningCoe]
          exact c.mem_edges_toSubgraph.mpr hcEdge
        exact (p'.append q'.reverse).mem_edges_toSubgraph.mp hdSet
      simp only [Walk.edges_append, List.mem_append] at hdEdge
      rcases hdEdge with hpEdge | hqEdge
      · exact hpSub.edges_subset hpEdge
      · have hq : e ∈ q'.edges := by simpa using hqEdge
        have harcEdge := hqSub.edges_subset hq
        have hdisj := hc.isTrail.disjoint_edges_takeUntil_dropUntil hbC
        exact False.elim (List.disjoint_left.mp hdisj.symm he harcEdge)
    have hrBack : r = back.reverse := by
      apply isPath_eq_of_edge_subset hr hback.reverse
      intro e he
      have heBack : e ∈ back.edges := by simpa using he
      exact hbackSub e heBack
    refine ⟨arc.reverse, ?_, ?_, ?_, ?_, ?_⟩
    · exact harc.reverse
    · simpa [hrBack, arc, back, Walk.edges_reverse] using
        (hc.isTrail.disjoint_edges_takeUntil_dropUntil hbC).symm
    · intro e he
      have hmem : e ∈ arc.edges ∨ e ∈ back.edges := by
        have hwalk := congrArg Walk.edges hsplit
        simp only [Walk.edges_append] at hwalk
        rw [← hwalk] at he
        exact List.mem_append.mp he
      rcases hmem with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl (by simpa [hrBack] using h)
    · intro e he
      rcases he with he | he
      · exact hrc e he
      · have ha : e ∈ arc.edges := by simpa using he
        exact c.edges_takeUntil_subset_edges hbC ha
    · have happ : r.append arc.reverse = c.reverse := by
        rw [hrBack, ← Walk.reverse_append, hsplit]
      rw [happ]
      exact hc.reverse

end PottsContinuity.FKC.Medial
