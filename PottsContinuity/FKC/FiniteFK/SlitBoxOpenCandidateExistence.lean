-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxOpenCandidateExistence.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open SimpleGraph

private theorem walk_exists_openGraph_of_all_edges_open
    {V : Type*} {G : SimpleGraph V} (A : Configuration G)
    {x y : V} (w : G.Walk x y)
    (hopen : ∀ e, e ∈ w.edges → e ∈ openEdges G A) :
    Nonempty ((openGraph G A).Walk x y) := by
  induction w with
  | nil => exact ⟨.nil⟩
  | @cons x z y hxz tail ih =>
      have hxzOpen : (openGraph G A).Adj x z :=
        (openGraph_adj G A x z).2 (hopen (s(x,z)) (by simp))
      have htail : ∀ e, e ∈ tail.edges → e ∈ openEdges G A := by
        intro e he
        exact hopen e (by simp [he])
      obtain ⟨tailOpen⟩ := ih htail
      exact ⟨.cons hxzOpen tailOpen⟩

private theorem openEdges_mem_configuration
    {V : Type*} {G : SimpleGraph V} (A : Configuration G)
    (e : G.edgeSet) (he : e.val ∈ openEdges G A) : e ∈ A := by
  rcases he with ⟨f, hf, hfe⟩
  have hEq : e = f := Subtype.ext hfe.symm
  rw [hEq]
  exact hf

/-- A configuration contains the original path support of some genuine
first-hit slit-box candidate exactly when the wired arc is actually reachable
by open slit-graph edges. This includes the nil-path case when the start is
already on the wired arc. -/
theorem slitBoxFirstHitCandidate_exists_open_iff_actualConnected
    (n : ℕ) (u : SlitBoxVertex n) (A : Configuration (slitBoxGraph n)) :
    (∃ p : SlitBoxFirstHitBaseCandidates n u,
      slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A) ↔
    ∃ t ∈ slitBoxWiredArc n, ActualConnected (slitBoxGraph n) A u t := by
  classical
  constructor
  · rintro ⟨p, hpOpen⟩
    have hEdgesOpen : ∀ e, e ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges →
        e ∈ openEdges (slitBoxGraph n) A := by
      intro e he
      have heGraph : e ∈ (slitBoxGraph n).edgeSet :=
        (p.val.2 : (slitBoxGraph n).Walk u p.val.1).edges_subset_edgeSet he
      let eGraph : (slitBoxGraph n).edgeSet := ⟨e, heGraph⟩
      have hsupport : eGraph ∈ slitBoxCandidateOriginalPathEdgeSupport n u p := by
        apply (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p eGraph).2
        simpa [eGraph] using he
      have hA : eGraph ∈ A := hpOpen hsupport
      exact ⟨eGraph, hA, rfl⟩
    have hwalk := walk_exists_openGraph_of_all_edges_open A
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1) hEdgesOpen
    exact ⟨p.val.1, p.property.1,
      (actualConnected_iff_walk (slitBoxGraph n) A u p.val.1).2 hwalk⟩
  · rintro ⟨t, ht, hconn⟩
    obtain ⟨b, hb, q, hq, hfirst⟩ :=
      actualConnected_exists_first_hit_path A ⟨t, ht, hconn⟩
    let f : openGraph (slitBoxGraph n) A →g slitBoxGraph n := {
      toFun := id
      map_rel' := by
        intro x y hxy
        exact openGraph_le (slitBoxGraph n) A hxy }
    let w : (slitBoxGraph n).Walk u b := q.map f
    have hwPath : w.IsPath := by
      exact hq.map (by intro x y hxy; exact hxy)
    have hfirstBase : ∀ x ∈ w.support,
        x ∈ (slitBoxWiredArc n : Set (SlitBoxVertex n)) → x = b := by
      intro x hx hxArc
      have hxQ : x ∈ q.support := by
        simpa [w, f, SimpleGraph.Walk.support_map] using hx
      exact hfirst x hxQ hxArc
    let base : FiniteSimplePathCarrier (slitBoxGraph n) u := ⟨b, ⟨w, hwPath⟩⟩
    let p : SlitBoxFirstHitBaseCandidates n u := ⟨base, hb, by
      simpa [finiteSimplePathSupport, base, w, f, SimpleGraph.Walk.support_map] using hfirstBase⟩
    have hPathEdgesEq : w.edges = q.edges := by
      simp [w, f, SimpleGraph.Walk.edges_map]
    have hSupportOpen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A := by
      apply (slitBoxCandidateOriginalPathEdgeSupport_subset_iff n u p A).2
      intro e he
      have heQ : e.val ∈ q.edges := by rw [← hPathEdgesEq]; exact he
      have heOpenGraph : e.val ∈ (openGraph (slitBoxGraph n) A).edgeSet :=
        q.edges_subset_edgeSet heQ
      have heOpen : e.val ∈ openEdges (slitBoxGraph n) A := by
        rwa [openGraph_edgeSet] at heOpenGraph
      exact openEdges_mem_configuration A e heOpen
    exact ⟨p, hSupportOpen⟩

end PottsContinuity.FKC.FiniteFK
