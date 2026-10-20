module

public import PottsContinuity.FKC.FiniteFK.BoundarySeedComplementFreeLaw
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Cluster-complement conditioning for every real q ≥ 1

The exploration geometry is imported unchanged from FKC. The probability law
below uses PD.Parameters, so it has no q < 4 restriction. The conditional-law
proof is adapted from FKC.FiniteFK.WiredAvoidingClusterComplement; it uses the
all-parameter PD conditional embedded law rather than the ClusterWeight law.
This is a supporting step in the proof of DCST Lemma 5, not Lemma 5 itself.
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedComplementLawVertexFintype : Fintype V := Fintype.ofFinite V
local instance seedComplementLawEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedComplementLawEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The exact induced-complement law for a stable actual-cluster record, with
all recorded open connections retained in its pulled-back boundary partition. -/
theorem law_filter_clusterRecord_map_complement_allq
    (q : Parameters) (ξ : BoundaryCondition V) (W : Set V) (S : Finset V)
    (A₀ : Configuration G) :
    ((law G q ξ).filter
      (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S)
          (fun C C' hagree => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
        exact frozenStateEvent_support q ξ (FKC.FiniteFK.wiredAvoidingClusterReveal G W S A₀)
          (revealRecordConfiguration (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀))).map
        (embeddedConfigurationRestriction
          (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G W S A₀)) G
          (FKC.FiniteFK.wiredAvoidingComplementEmbedding G W S A₀)
          (FKC.FiniteFK.wiredAvoidingComplementGraph_le (G := G) W S A₀)) =
      law (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G W S A₀)) q
        (isolatedExtensionPullbackBoundary (FKC.FiniteFK.wiredAvoidingComplementEmbedding G W S A₀)
          (frozenBoundary ξ
            (revealRecordConfiguration (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀).val)) := by
  let C := FKC.FiniteFK.wiredAvoidingComplementSet G W S A₀
  let f := FKC.FiniteFK.wiredAvoidingComplementEmbedding G W S A₀
  let H := (G.induce C).map f
  let R := FKC.FiniteFK.wiredAvoidingClusterReveal G W S A₀
  let K := revealRecordConfiguration (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀
  have hR : R = subgraphRemovedEdges H G := by
    simpa [R, H, C, f, FKC.FiniteFK.wiredAvoidingComplementSet,
      subgraphRemovedEdges, FKC.FiniteFK.subgraphRemovedEdges] using FKC.FiniteFK.wiredAvoidingClusterReveal_eq_subgraphRemovedEdges (G := G) W S A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    rw [← hR]
    exact K.property
  have hHG : H ≤ G := FKC.FiniteFK.wiredAvoidingComplementGraph_le (G := G) W S A₀
  have hconditional := law_filter_frozen_map_embeddedRestriction
    (G.induce C) G f hHG q ξ K'
  have hevent : revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S)
      (fun C C' hagree => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
    ext C'
    simp [frozenStateEvent, K', K, R, hR]
  have hfiltered :
      (law G q ξ).filter (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G W S)
            (fun C C' hagree => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
          exact frozenStateEvent_support q ξ (FKC.FiniteFK.wiredAvoidingClusterReveal G W S A₀)
            (revealRecordConfiguration (FKC.FiniteFK.wiredAvoidingClusterReveal G W S) A₀)) =
      (law G q ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    ext C'
    rw [PMF.filter_apply, PMF.filter_apply, hevent]
  have hfilter := congrArg
    (fun P : PMF (Configuration G) =>
      PMF.map (embeddedConfigurationRestriction (G.induce C) G f hHG) P) hfiltered
  simpa [H, f, K, R, C, K', FKC.FiniteFK.wiredAvoidingComplementSet, isolatedExtensionPullbackBoundary, hR] using
    hfilter.trans hconditional


/-- Exploring all designated boundary vertices leaves a discrete partition on
its complement. This uses only the combinatorial FKC theorem, independently
of any probabilistic restriction on the cluster weight. -/
theorem boundarySeedComplement_partition_eq_bot_allq
    (ξ : BoundaryCondition V) (A₀ : Configuration G) :
    (isolatedExtensionPullbackBoundary
      (FKC.FiniteFK.wiredAvoidingComplementEmbedding G ∅ ξ.boundary.toFinset A₀)
      (frozenBoundary ξ
        (revealRecordConfiguration
          (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset) A₀).val)).partition
        = ⊥ := by
  let ξ' : FKC.FiniteFK.BoundaryCondition V := ⟨ξ.boundary, ξ.partition, ξ.supported⟩
  have h := FKC.FiniteFK.boundarySeedComplement_frozenPartition_eq_bot (G := G) ξ' A₀
  exact h

/-- The complement of the actual clusters of every designated boundary vertex
has exactly the free FK law, for every independent edge parameter and q ≥ 1.
The original partition may be any partition supported on that boundary. -/
theorem law_filter_boundarySeedRecord_map_complement_eq_free_allq
    (θ : Parameters) (ξ : BoundaryCondition V) (A₀ : Configuration G) :
    ((law G θ ξ).filter
      (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent
          (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset)
          (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
            (∅ : Set V) ξ.boundary.toFinset A B h) A₀]
        exact frozenStateEvent_support θ ξ _ _)).map
        (embeddedConfigurationRestriction
          (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀)) G
          (FKC.FiniteFK.wiredAvoidingComplementEmbedding G ∅ ξ.boundary.toFinset A₀)
          (FKC.FiniteFK.wiredAvoidingComplementGraph_le (G := G) ∅ ξ.boundary.toFinset A₀)) =
      law (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀)) θ
        (BoundaryCondition.free ∅) := by
  rw [law_filter_clusterRecord_map_complement_allq]
  apply law_eq_of_boundary_partition_eq
  exact boundarySeedComplement_partition_eq_bot_allq ξ A₀

end
end PottsContinuity.RSW
