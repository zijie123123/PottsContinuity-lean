module

public import PottsContinuity.BD12.EmbeddingPartition
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-! The canonical edge partition of an embedded graph. Its projection is the
shared literal restriction, not a conditional law with exterior edges closed. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
local instance graphPartitionInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance graphPartitionOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance graphPartitionInnerEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance graphPartitionOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- The complement consists exactly of outer edges outside the embedded inner graph. -/
def graphInnerEdgePartition :
    G.edgeSet ⊕ {a : H.edgeSet // a ∉ Set.range (FKC.FiniteFK.embeddedEdgeEmbedding G H f hGH)} ≃ H.edgeSet :=
  finiteEmbeddingPartition (FKC.FiniteFK.embeddedEdgeEmbedding G H f hGH)

omit [Finite V] [Finite W] in
/-- The marginal projection reads exactly the states of the embedded original edges. -/
theorem graphInnerEdgePartition_projection (C : PD.FK.Configuration H) :
    finitePartitionProjection (graphInnerEdgePartition G H f hGH) C =
      FKC.FiniteFK.embeddedConfigurationRestriction G H f hGH C := by
  ext a
  exact (finiteEmbeddingPartition_projection_mem _ C a).trans
    (FKC.FiniteFK.mem_embeddedConfigurationRestriction G H f hGH C a).symm

end
end PottsContinuity.BD12
