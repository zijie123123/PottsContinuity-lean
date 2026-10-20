module

public import PottsContinuity.Thm3.Push.TwoRevealActiveCarrier
public import PottsContinuity.Thm3.Push.AttachmentLabelBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance twoRevealExteriorEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Every state of the two disjoint exteriors induces at most the two
separately wired actual active attachment classes. The only boundary input
is literal preservation of the explicit ambient labels. -/
theorem twoReveal_exterior_partitions_le_of_boundary_labels
    {V : Type*} [Finite V] (G : SimpleGraph V) (L R : Configuration G)
    (hd : Disjoint (revealIncidentVertices G L) (revealIncidentVertices G R))
    (ξ : BoundaryCondition V)
    (hboundary : ∀ u v, ξ.partition.r u v →
      twoArcAttachmentLabel (revealIncidentVertices G L) (revealIncidentVertices G R) u =
      twoArcAttachmentLabel (revealIncidentVertices G L) (revealIncidentVertices G R) v) :
    ∀ K : RemovedConfiguration G (L ∪ R),
      (isolatedExtensionPullbackBoundary (Function.Embedding.subtype _)
        (frozenBoundary ξ K.val)).partition ≤ (twoRevealActiveBoundary G L R hd).partition := by
  let f : unexaminedVertices G (L ∪ R) ↪ V := Function.Embedding.subtype _
  let label := twoArcAttachmentLabel (revealIncidentVertices G L) (revealIncidentVertices G R)
  let j := twoArcAttachmentQuotientEmbedding f (revealIncidentVertices G L) (revealIncidentVertices G R) hd
  apply all_frozen_pullback_partitions_le_of_attachment_labels G f ξ
    (twoRevealActiveBoundary G L R hd) (L ∪ R) label j
  · intro v
    exact (twoArcAttachmentQuotientEmbedding_apply f _ _ hd v).symm
  · exact hboundary
  · intro e he u v hpair
    have hue : u ∈ e.val := by rw [hpair]; exact Sym2.mem_mk_left _ _
    have hve : v ∈ e.val := by rw [hpair]; exact Sym2.mem_mk_right _ _
    apply (twoArcAttachmentLabel_eq_iff _ _ hd u v).mpr
    rcases Finset.mem_union.mp he with he | he
    · exact Or.inr (Or.inl ⟨⟨e,he,hue⟩,⟨e,he,hve⟩⟩)
    · exact Or.inr (Or.inr ⟨⟨e,he,hue⟩,⟨e,he,hve⟩⟩)

/-- The exact active graph has that same all-state comparison: its removed
edge carrier is proved equal to the original joint reveal. -/
theorem twoReveal_active_exterior_partitions_le_of_boundary_labels
    {V : Type*} [Finite V] (G : SimpleGraph V) (L R : Configuration G)
    (hd : Disjoint (revealIncidentVertices G L) (revealIncidentVertices G R))
    (ξ : BoundaryCondition V)
    (hboundary : ∀ u v, ξ.partition.r u v →
      twoArcAttachmentLabel (revealIncidentVertices G L) (revealIncidentVertices G R) u =
      twoArcAttachmentLabel (revealIncidentVertices G L) (revealIncidentVertices G R) v) :
    ∀ K : RemovedConfiguration G (subgraphRemovedEdges
      ((activeUnexaminedGraph G (L ∪ R)).map (Function.Embedding.subtype _)) G),
      (isolatedExtensionPullbackBoundary (Function.Embedding.subtype _)
        (frozenBoundary ξ K.val)).partition ≤ (twoRevealActiveBoundary G L R hd).partition := by
  rw [activeUnexaminedGraph_removedEdges]
  exact twoReveal_exterior_partitions_le_of_boundary_labels G L R hd ξ hboundary

end
end PottsContinuity.Push
