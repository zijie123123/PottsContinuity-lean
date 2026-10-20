-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ClusterRemainingGraph.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterExploration
public import PottsContinuity.FKC.FiniteFK.EdgeRestriction

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Vertices outside a seed's actual open cluster, as a genuine subtype of the
original vertex carrier. -/
def actualClusterComplementSet (v : V) (A : Configuration G) : Set V :=
  {u | ¬ ActualConnected G A v u}

def actualClusterComplementEmbedding (v : V) (A : Configuration G) :
    actualClusterComplementSet v A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgeRestriction_actualClusterReveal_eq_induced_complement
    (v : V) (A : Configuration G) :
    edgeRestriction G (actualClusterReveal G v A) =
      (G.induce (actualClusterComplementSet v A)).map
        (actualClusterComplementEmbedding v A) := by
  ext x y
  constructor
  · intro hxy
    have hxy' : G.Adj x y ∧ s(x,y) ∉ openEdges G (actualClusterReveal G v A) := by
      simpa [edgeRestriction] using hxy
    rcases hxy' with ⟨hAdj, hNot⟩
    have hnotConn : ¬ ActualConnected G A v x ∧ ¬ ActualConnected G A v y := by
      constructor
      · intro hx
        apply hNot
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualClusterReveal G v A := by
          rw [actualClusterReveal_mem_iff]
          exact ⟨x, (Sym2.mem_iff').2 (Or.inl rfl), hx⟩
        have hOpen := (coe_mem_openEdges_iff G (actualClusterReveal G v A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        simpa using hOpen
      · intro hy
        apply hNot
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualClusterReveal G v A := by
          rw [actualClusterReveal_mem_iff]
          exact ⟨y, (Sym2.mem_iff').2 (Or.inr rfl), hy⟩
        have hOpen := (coe_mem_openEdges_iff G (actualClusterReveal G v A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        simpa using hOpen
    apply (SimpleGraph.map_adj (actualClusterComplementEmbedding v A)
      (G.induce (actualClusterComplementSet v A)) x y).2
    refine ⟨⟨x, hnotConn.1⟩, ⟨y, hnotConn.2⟩, ?_, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mpr hAdj
  · intro hxy
    rcases (SimpleGraph.map_adj (actualClusterComplementEmbedding v A)
      (G.induce (actualClusterComplementSet v A)) x y).1 hxy with
      ⟨u, w, hAdjInduced, hux, hwy⟩
    have hAdj : G.Adj u.val w.val := SimpleGraph.induce_adj.mp hAdjInduced
    have hux' : u.val = x := hux
    have hwy' : w.val = y := hwy
    subst x
    subst y
    rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro hmem
    have hR : (⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
        actualClusterReveal G v A := by
      apply (coe_mem_openEdges_iff G (actualClusterReveal G v A)
        ⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩).mp
      simpa [actualClusterComplementEmbedding] using hmem
    rcases (actualClusterReveal_mem_iff G v A _).mp hR with ⟨z, hz, hconn⟩
    rcases (Sym2.mem_iff').mp hz with hzu | hzw
    · exact u.2 (hzu ▸ hconn)
    · exact w.2 (hzw ▸ hconn)

end
end PottsContinuity.FKC.FiniteFK
