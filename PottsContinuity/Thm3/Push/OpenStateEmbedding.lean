module

public import PottsContinuity.Thm3.Push.CrossingRestriction

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- The adjacency test on Boolean open edges works on infinite carriers too. -/
theorem booleanOpenGraph_adj {V : Type*} (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (u v : V) :
    (SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, ω ⟨e,h⟩ = true}).Adj u v ↔
      ∃ h : s(u,v) ∈ G.edgeSet, ω ⟨s(u,v),h⟩ = true := by
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact And.left
  · rintro ⟨he, ho⟩
    exact ⟨⟨he, ho⟩, (G.mem_edgeSet.mp he).ne⟩

/-- An embedding preserving the actual Boolean bond states embeds the open
finite graph in the corresponding open graph, even if the latter is infinite.
Proof pattern adapted from Foundations.HorizontalCrossingBridge's private
openGraphAdj_restriction, with the infinite target handled directly. -/
def openStateEmbedding {V W : Type*} [Finite V] {G : SimpleGraph V}
    {H : SimpleGraph W} (j : G ↪g H) (ωG : G.edgeSet → Bool) (ωH : H.edgeSet → Bool)
    (hstate : ∀ e, ωG e = ωH (j.mapEdgeSet e)) :
    openGraph G (boolConfigurationEquiv G ωG) ↪g
      SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ H.edgeSet, ωH ⟨e,h⟩ = true} where
  toFun := j
  inj' := j.injective
  map_rel_iff' := by
    intro u v
    rw [booleanOpenGraph_adj, openGraph_adj, openEdges_boolConfigurationEquiv]
    change (∃ he, ωH ⟨s(j u,j v),he⟩ = true) ↔
      ∃ he, ωG ⟨s(u,v),he⟩ = true
    constructor
    · rintro ⟨he, ho⟩
      have hs := G.mem_edgeSet.mpr (j.map_rel_iff'.mp (H.mem_edgeSet.mp he))
      refine ⟨hs, ?_⟩
      have heq : j.mapEdgeSet ⟨s(u,v),hs⟩ = ⟨s(j u,j v),he⟩ := by
        apply Subtype.ext
        simp
      rw [hstate, heq]
      exact ho
    · rintro ⟨he, ho⟩
      have ht := H.mem_edgeSet.mpr (j.map_rel_iff'.mpr (G.mem_edgeSet.mp he))
      refine ⟨ht, ?_⟩
      have heq : j.mapEdgeSet ⟨s(u,v),he⟩ = ⟨s(j u,j v),ht⟩ := by
        apply Subtype.ext
        simp
      rw [← heq, ← hstate]
      exact ho

end
end PottsContinuity.Push
