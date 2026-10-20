module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
-- Generalization of FKC/FiniteFK/MultiSeedClusterExploration's complement-law
-- proof to independent interior edge parameters and every real cluster weight ≥1.

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance multiSeedComplementLawEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance multiSeedComplementLawEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The actual multi-seed exploration leaves an exact induced-complement FK
law for every admissible parameter, retaining the entire frozen partition. -/
theorem law_filter_seedRecord_map_complement_allParameters
    (q : Parameters) (ξ : BoundaryCondition V) (S : Finset V)
    (A₀ : Configuration G) :
    ((law G q ξ).filter
      (Exploration.revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.actualMultiClusterReveal G S)
          (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A₀]
        exact frozenStateEvent_support q ξ (FKC.FiniteFK.actualMultiClusterReveal G S A₀)
          (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A₀))).map
        (embeddedConfigurationRestriction
          (G.induce (FKC.FiniteFK.actualMultiClusterComplementSet G S A₀)) G
          (FKC.FiniteFK.actualMultiClusterComplementEmbedding G S A₀)
          (FKC.FiniteFK.actualMultiClusterComplementGraph_le (G := G) S A₀)) =
      law (G.induce (FKC.FiniteFK.actualMultiClusterComplementSet G S A₀)) q
        (isolatedExtensionPullbackBoundary (FKC.FiniteFK.actualMultiClusterComplementEmbedding G S A₀)
          (frozenBoundary ξ
            (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A₀).val)) := by
  let C := FKC.FiniteFK.actualMultiClusterComplementSet G S A₀
  let f := FKC.FiniteFK.actualMultiClusterComplementEmbedding G S A₀
  let H := (G.induce C).map f
  let R := FKC.FiniteFK.actualMultiClusterReveal G S A₀
  let K := Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A₀
  have hR : R = subgraphRemovedEdges H G := by
    calc
      R = FKC.FiniteFK.subgraphRemovedEdges H G :=
        FKC.FiniteFK.actualMultiClusterReveal_eq_subgraphRemovedEdges S A₀
      _ = subgraphRemovedEdges H G := by
        ext e
        rw [FKC.FiniteFK.mem_subgraphRemovedEdges,mem_subgraphRemovedEdges]
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    rw [← hR]
    exact K.property
  have hHG : H ≤ G := by
    change (G.induce (FKC.FiniteFK.actualMultiClusterComplementSet G S A₀)).map
      (FKC.FiniteFK.actualMultiClusterComplementEmbedding G S A₀) ≤ G
    exact FKC.FiniteFK.actualMultiClusterComplementGraph_le (G := G) S A₀
  have hconditional := law_filter_frozen_map_embeddedRestriction
    (G.induce C) G f hHG q ξ K'
  have hevent : Exploration.revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.actualMultiClusterReveal G S)
      (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A₀]
    ext C'
    simp [frozenStateEvent, K', K, R, hR]
  have hfiltered :
      (law G q ξ).filter (Exploration.revealRecordEvent (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)
        (by
          rw [Exploration.revealRecordEvent_eq_frozenStateEvent (FKC.FiniteFK.actualMultiClusterReveal G S)
            (FKC.FiniteFK.actualMultiClusterReveal_consistent S) A₀]
          exact frozenStateEvent_support q ξ (FKC.FiniteFK.actualMultiClusterReveal G S A₀)
            (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A₀)) =
      (law G q ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    ext C'
    rw [PMF.filter_apply, PMF.filter_apply, hevent]
  have hfilter := congrArg
    (fun P : PMF (Configuration G) =>
      PMF.map (embeddedConfigurationRestriction (G.induce C) G f hHG) P) hfiltered
  simpa [H, f, K, R, C, K', isolatedExtensionPullbackBoundary, hR] using
    hfilter.trans hconditional


end
end PottsContinuity.RSW
