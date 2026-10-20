-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ClusterComplementLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.ClusterRemainingGraph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The actual revealed edge set is exactly the set of original edges removed
when restricting to the induced graph outside the revealed cluster. -/
theorem actualClusterReveal_eq_subgraphRemovedEdges
    (v : V) (A : Configuration G) :
    actualClusterReveal G v A =
      subgraphRemovedEdges
        ((G.induce (actualClusterComplementSet v A)).map
          (actualClusterComplementEmbedding v A)) G := by
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges]
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_actualClusterReveal_eq_induced_complement (G := G) v A)
  rw [edgeRestriction_edgeSet] at hgraph
  rw [← hgraph]
  simp only [Set.mem_sdiff]
  simp [e.property, coe_mem_openEdges_iff]

theorem actualClusterComplementGraph_le
    (v : V) (A : Configuration G) :
    ((G.induce (actualClusterComplementSet v A)).map
      (actualClusterComplementEmbedding v A)) ≤ G := by
  rw [← edgeRestriction_actualClusterReveal_eq_induced_complement (G := G) v A]
  exact edgeRestriction_le G (actualClusterReveal G v A)

end
end PottsContinuity.FKC.FiniteFK
