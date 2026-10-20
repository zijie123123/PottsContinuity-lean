-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SimplePathEdgeSetUniqueness.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open SimpleGraph

theorem simplePath_support_eq_of_edgeMembership_eq
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk u w)
    (hp : p.IsPath) (hq : q.IsPath)
    (hedges : ∀ e : Sym2 V, e ∈ p.edges ↔ e ∈ q.edges) :
    p.support = q.support ∧ v = w := by
  induction p generalizing w with
  | nil =>
      have hqEdges : q.edges = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro e he
        have hempty : e ∈ (SimpleGraph.Walk.nil : G.Walk u u).edges := by
          simpa using (hedges e).mpr he
        simp at hempty
      have hqNil : q.Nil := q.edges_eq_nil.mp hqEdges
      cases q with
      | nil => exact ⟨rfl, rfl⟩
      | cons hq' q' => simp at hqNil
  | @cons u v z hpAdj p' ih =>
      have hfirst : s(u, v) ∈ (SimpleGraph.Walk.cons hpAdj p').edges := by simp
      have hfirstQ : s(u, v) ∈ q.edges := (hedges _).mp hfirst
      cases q with
      | nil => simp at hfirstQ
      | @cons u a w hqAdj q' =>
          have hqPath := (SimpleGraph.Walk.cons_isPath_iff hqAdj q').mp hq
          have hvertex : v = a := by
            have h := hq.eq_snd_of_mem_edges hfirstQ
            simpa using h
          subst a
          have hpPath := (SimpleGraph.Walk.cons_isPath_iff hpAdj p').mp hp
          have hpEdgesNodup : (Walk.cons hpAdj p').edges.Nodup :=
            SimpleGraph.Walk.edges_nodup_of_support_nodup hp.support_nodup
          have hqEdgesNodup : (Walk.cons hqAdj q').edges.Nodup :=
            SimpleGraph.Walk.edges_nodup_of_support_nodup hq.support_nodup
          rw [SimpleGraph.Walk.edges_cons] at hpEdgesNodup hqEdgesNodup
          simp only [List.nodup_cons] at hpEdgesNodup hqEdgesNodup
          have hpNoHead : s(u, v) ∉ p'.edges := hpEdgesNodup.1
          have hqNoHead : s(u, v) ∉ q'.edges := hqEdgesNodup.1
          have htail : ∀ e : Sym2 V, e ∈ p'.edges ↔ e ∈ q'.edges := by
            intro e
            constructor
            · intro he
              have heFull : e ∈ (SimpleGraph.Walk.cons hpAdj p').edges := by
                simp [he]
              have heQ := (hedges e).mp heFull
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at heQ
              rcases heQ with heHead | heTail
              · subst e
                exact False.elim (hpNoHead he)
              · exact heTail
            · intro he
              have heFull : e ∈ (SimpleGraph.Walk.cons hqAdj q').edges := by
                simp [he]
              have heP := (hedges e).mpr heFull
              rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at heP
              rcases heP with heHead | heTail
              · subst e
                exact False.elim (hqNoHead he)
              · exact heTail
          obtain ⟨hsupport, hend⟩ := ih q' hpPath.1 hqPath.1 htail
          constructor
          · simp [SimpleGraph.Walk.support_cons, hsupport]
          · exact hend

end PottsContinuity.FKC.FiniteFK
