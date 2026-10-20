module

public import PottsContinuity.Thm3.RSW.SeedComplementFreeBoundary
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Exact free law on the unexplored complement of boundary-rooted clusters -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedComplementFreeLawEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedComplementFreeLawEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Exploring all actual clusters from a seed set containing the original
boundary leaves the exact free FK law on the induced unexplored complement.
The complete record, its states and its actual support are explicit. -/
theorem law_filter_seedRecord_map_complement_free
    (θ : Parameters) (ξ : BoundaryCondition V) (S : Finset V)
    (hseeds : ∀ u ∈ ξ.boundary, u ∈ S) (A : Configuration G) :
    ((law G θ ξ).filter
      (Exploration.revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (FKC.FiniteFK.actualMultiClusterReveal G S)
          (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A]
        exact frozenStateEvent_support θ ξ (FKC.FiniteFK.actualMultiClusterReveal G S A)
          (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A))).map
        (embeddedConfigurationRestriction
          (G.induce (FKC.FiniteFK.actualMultiClusterComplementSet G S A)) G
          (FKC.FiniteFK.actualMultiClusterComplementEmbedding G S A)
          (FKC.FiniteFK.actualMultiClusterComplementGraph_le (G := G) S A)) =
      law (G.induce (FKC.FiniteFK.actualMultiClusterComplementSet G S A)) θ
        (BoundaryCondition.free ∅) := by
  rw [law_filter_seedRecord_map_complement_allParameters]
  apply law_eq_of_boundary_partition_eq
  apply Setoid.ext
  intro u v
  change (frozenBoundary ξ
    (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A).val).partition.r
      u.val v.val ↔ u = v
  exact (seedComplement_frozen_partition_free ξ S A hseeds u.property v.property).trans
    Subtype.val_injective.eq_iff

end
end PottsContinuity.RSW
