module

public import PottsContinuity.Thm3.Push.TwoRevealActiveCarrier
public import PottsContinuity.PlanarTopology.BoundaryWalkClipping
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance twoRevealSegmentEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

private theorem clipped_edge_not_revealed {V : Type*} (G H : SimpleGraph V)
    (L R : Configuration G) {x y : V} (q : H.Walk x y)
    (hL : ∀ z ∈ q.support, z ∈ revealIncidentVertices G L → z=x)
    (hR : ∀ z ∈ q.support, z ∈ revealIncidentVertices G R → z=y)
    (e : G.edgeSet) (he : e.val ∈ q.edges) : e ∉ L ∪ R := by
  let a := e.val.out.1
  let b := e.val.out.2
  have hpair : s(a,b)=e.val := Quot.out_eq _
  have ha : a ∈ e.val := by rw [← hpair]; exact Sym2.mem_mk_left _ _
  have hb : b ∈ e.val := by rw [← hpair]; exact Sym2.mem_mk_right _ _
  have hqa := SimpleGraph.Walk.mem_support_of_mem_edges he ha
  have hqb := SimpleGraph.Walk.mem_support_of_mem_edges he hb
  have hne : a ≠ b := (G.mem_edgeSet.mp (hpair.symm ▸ e.property)).ne
  intro hmem
  rcases Finset.mem_union.mp hmem with heL | heR
  · exact hne ((hL a hqa ⟨e,heL,ha⟩).trans (hL b hqb ⟨e,heL,hb⟩).symm)
  · exact hne ((hR a hqa ⟨e,heR,ha⟩).trans (hR b hqb ⟨e,heR,hb⟩).symm)

/-- Clip an actual open crossing between the two disjoint exterior vertex
sets. Every retained edge is genuinely unexamined and every retained vertex
is active. No planar or probability premise is needed for this step. -/
theorem twoReveal_crossing_remaining_segment {V : Type*} (G : SimpleGraph V)
    (L R : Configuration G)
    (hd : Disjoint (revealIncidentVertices G L) (revealIncidentVertices G R))
    (C : Configuration G) {u v : V}
    (p : (openGraph G C).Walk u v)
    (hu : u ∈ revealIncidentVertices G L) (hv : v ∈ revealIncidentVertices G R) :
    ∃ x ∈ revealIncidentVertices G L, ∃ y ∈ revealIncidentVertices G R,
      ∃ q : (openGraph G C).Walk x y,
        (∀ e : G.edgeSet, e.val ∈ q.edges → e ∉ L ∪ R) ∧
        ∀ z ∈ q.support, z ∈ unexaminedVertices G (L ∪ R) := by
  obtain ⟨x,hx,y,hy,q,hqp,hL,hR⟩ := PlanarTopology.walk_subwalk_between_sets p
    (revealIncidentVertices G L) (revealIncidentVertices G R) hu hv
  have hnot := clipped_edge_not_revealed G (openGraph G C) L R q hL hR
  have hnil : ¬ q.Nil := by
    intro hn
    exact Set.disjoint_left.mp hd hx (hn.eq.symm ▸ hy)
  refine ⟨x,hx,y,hy,q,hnot,?_⟩
  intro z hz
  obtain ⟨e,he,hze⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hz
  have heopen := q.edges_subset_edgeSet he
  rw [openGraph_edgeSet] at heopen
  let f : G.edgeSet := ⟨e,openEdges_subset G C heopen⟩
  exact ⟨f,hnot f he,hze⟩

end
end PottsContinuity.Push
