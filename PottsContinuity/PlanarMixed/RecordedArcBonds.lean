module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourcePaths
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

/-! Exposed original arc bonds retain their actual open states in the
complete stopping record. No frozen-state equality is supplied. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK Exploration
noncomputable section
local instance recordedArcBondsEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Any deliberately removed original bond belongs to the host complement
of the embedded active graph. -/
theorem embedded_removed_bond_exposed {V U : Type*} [Finite V] [Finite U]
    (G : SimpleGraph V) (H : SimpleGraph U) (i : V ↪ U) (h : G.map i ≤ H)
    (R : Configuration G) (e : G.edgeSet) (he : e ∈ R) :
    embeddedEdgeEmbedding G H i h e ∈
      subgraphRemovedEdges ((edgeRestriction G R).map i) H := by
  rw [mem_subgraphRemovedEdges,SimpleGraph.edgeSet_map]
  rintro ⟨b,hb,hbe⟩
  change i.sym2Map b = i.sym2Map e.val at hbe
  have hb' := i.sym2Map.injective hbe
  rw [hb'] at hb
  rw [edgeRestriction_edgeSet] at hb
  exact hb.2 ((coe_mem_openEdges_iff G R e).mpr he)

end
end PottsContinuity.PlanarMixed
