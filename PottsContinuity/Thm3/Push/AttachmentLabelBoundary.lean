module

public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- Labels preserved by every permitted removed edge and by original boundary
joins are also preserved by the complete frozen partition. -/
theorem frozenBoundary_le_labelKernel_of_local
    {W L : Type*} (H : SimpleGraph W) (ξ : BoundaryCondition W)
    (R K : Configuration H) (hKR : K ⊆ R) (label : W → L)
    (hboundary : ∀ x y, ξ.partition.r x y → label x = label y)
    (hedge : ∀ (e : H.edgeSet), e ∈ R → ∀ x y,
      e.val = s(x,y) → label x = label y) :
    (frozenBoundary ξ K).partition ≤ Setoid.ker label := by
  apply componentSetoid_le
  · apply reachableSetoid_le_of_adj
    intro x y hxy
    obtain ⟨e,heK,hexy⟩ := (openGraph_adj H K x y).mp hxy
    exact hedge e (hKR heK) x y hexy
  · exact hboundary

/-- An exterior label extends distinct labels of the retained boundary
classes. Local edge and boundary invariance therefore bounds the actual
pulled-back frozen partition, retaining every original boundary join. -/
theorem frozen_pullback_partition_le_of_attachment_labels
    {V W L : Type*} (H : SimpleGraph W) (f : V ↪ W)
    (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (R K : Configuration H) (hKR : K ⊆ R)
    (label : W → L) (j : Quotient η.partition ↪ L)
    (hretained : ∀ v, label (f v) = j (Quotient.mk η.partition v))
    (hboundary : ∀ x y, ξ.partition.r x y → label x = label y)
    (hedge : ∀ (e : H.edgeSet), e ∈ R → ∀ x y,
      e.val = s(x,y) → label x = label y) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K)).partition ≤
      η.partition := by
  intro u v huv
  have hlabel := frozenBoundary_le_labelKernel_of_local H ξ R K hKR label
    hboundary hedge huv
  change label (f u) = label (f v) at hlabel
  rw [hretained u,hretained v] at hlabel
  exact Quotient.exact (j.injective hlabel)

/-- One deterministic attachment labeling works simultaneously for EVERY
state of the removed edges. No law or crossing estimate is a premise. -/
theorem all_frozen_pullback_partitions_le_of_attachment_labels
    {V W L : Type*} (H : SimpleGraph W) (f : V ↪ W)
    (ξ : BoundaryCondition W) (η : BoundaryCondition V) (R : Configuration H)
    (label : W → L) (j : Quotient η.partition ↪ L)
    (hretained : ∀ v, label (f v) = j (Quotient.mk η.partition v))
    (hboundary : ∀ x y, ξ.partition.r x y → label x = label y)
    (hedge : ∀ (e : H.edgeSet), e ∈ R → ∀ x y,
      e.val = s(x,y) → label x = label y) :
    ∀ K : RemovedConfiguration H R,
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
        η.partition := by
  intro K
  exact frozen_pullback_partition_le_of_attachment_labels H f ξ η R K.val
    K.property label j hretained hboundary hedge

end PottsContinuity.Push
