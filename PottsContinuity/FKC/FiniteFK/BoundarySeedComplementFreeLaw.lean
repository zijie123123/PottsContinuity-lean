-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/BoundarySeedComplementFreeLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterBoundary
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterComplement
public import PottsContinuity.FKC.FiniteFK.RectangleBottomCollar

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance boundarySeedVertexFintype : Fintype V := Fintype.ofFinite V
local instance boundarySeedEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundarySeedEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- If every original boundary vertex is used as a seed and the forbidden set
is empty, then the frozen boundary partition pulls back trivially to the
induced complement, for every actually attained record. -/
theorem boundarySeedComplement_frozenPartition_eq_bot
    (ξ : BoundaryCondition V) (A₀ : Configuration G) :
    (isolatedExtensionPullbackBoundary
      (wiredAvoidingComplementEmbedding G ∅ ξ.boundary.toFinset A₀)
      (frozenBoundary ξ
        (revealRecordConfiguration G
          (wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset) A₀).val)).partition = ⊥ := by
  let S : Finset V := ξ.boundary.toFinset
  let C := wiredAvoidingComplementSet G ∅ S A₀
  let f := wiredAvoidingComplementEmbedding G ∅ S A₀
  have hξ : ξ.boundary ⊆ wiredAvoidingClusterSet G ∅ S A₀ ∪ (∅ : Set V) := by
    have hseed : ∀ s ∈ S, s ∉ (∅ : Set V) := by simp
    have hcluster := wiredAvoidingClusterSet_seed_subset (W := (∅ : Set V)) S A₀ hseed
    intro v hv
    have hvS : v ∈ S := by
      simpa [S] using hv
    exact Set.mem_union_left _ (hcluster v hvS)
  have hdom := isolatedPullback_frozenWiredAvoidingClusterBoundary_le_wired
    ξ (∅ : Set V) S A₀ hξ
  have hbot :
      (BoundaryCondition.wired (f ⁻¹' (∅ : Set V))).partition = ⊥ := by
    ext u v
    simp [BoundaryCondition.wired_rel]
  have hle :
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary ξ
          (revealRecordConfiguration G
            (wiredAvoidingClusterReveal G (∅ : Set V) S) A₀).val)).partition ≤ ⊥ := by
    rw [← hbot]
    exact hdom
  exact le_antisymm hle bot_le

end
end PottsContinuity.FKC.FiniteFK
