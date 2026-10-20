module

public import PottsContinuity.Thm3.Prop4.ClusterReveal
public import PottsContinuity.FKC.FiniteFK.ClusterComplementLaw
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Exact all-q FK law on the induced complement of the actual cluster -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterComplementEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The genuine induced vertex carrier outside the actual open seed cluster. -/
def clusterComplement (u : V) (A : Configuration G) : Set V :=
  {v | ¬ ActualConnected G A u v}

/-- Literal inclusion of every surviving vertex. -/
def clusterComplementEmbedding (u : V) (A : Configuration G) : clusterComplement u A ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

/-- The remaining induced graph is an actual subgraph of the original graph. -/
theorem clusterComplement_map_le (u : V) (A : Configuration G) :
    ((G.induce (clusterComplement u A)).map (clusterComplementEmbedding u A)) ≤ G :=
  FKC.FiniteFK.actualClusterComplementGraph_le u A

/-- The stopped cluster reveal removes exactly the non-complement edges. -/
theorem clusterReveal_eq_removed (u : V) (A : Configuration G) :
    clusterReveal G u A = subgraphRemovedEdges
      ((G.induce (clusterComplement u A)).map (clusterComplementEmbedding u A)) G :=
  FKC.FiniteFK.actualClusterReveal_eq_subgraphRemovedEdges u A

/-- Exact conditional law in the induced cluster complement at independent parameters. -/
theorem law_filter_clusterRecord_map_complement (θ : Parameters) (ξ : BoundaryCondition V)
    (u : V) (A₀ : Configuration G) :
    ((law G θ ξ).filter (Exploration.revealRecordEvent (clusterReveal G u) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (clusterReveal G u) (clusterReveal_stable G u) A₀]
        exact frozenStateEvent_support θ ξ (clusterReveal G u A₀)
          (Exploration.revealRecordConfiguration (clusterReveal G u) A₀))).map
      (embeddedConfigurationRestriction (G.induce (clusterComplement u A₀)) G
        (clusterComplementEmbedding u A₀) (clusterComplement_map_le u A₀)) =
    law (G.induce (clusterComplement u A₀)) θ
      (isolatedExtensionPullbackBoundary (clusterComplementEmbedding u A₀)
        (frozenBoundary ξ (Exploration.revealRecordConfiguration (clusterReveal G u) A₀).val)) := by
  let C := clusterComplement u A₀
  let f := clusterComplementEmbedding u A₀
  let H := (G.induce C).map f
  let R := clusterReveal G u A₀
  let K := Exploration.revealRecordConfiguration (clusterReveal G u) A₀
  have hR : R = subgraphRemovedEdges H G := clusterReveal_eq_removed u A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) :=
    ⟨K.val,by rw [← hR]; exact K.property⟩
  have hevent : Exploration.revealRecordEvent (clusterReveal G u) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent
      (clusterReveal G u) (clusterReveal_stable G u) A₀]
    ext B
    simp [frozenStateEvent,K',K,R,hR]
  have hfiltered :
      (law G θ ξ).filter (Exploration.revealRecordEvent (clusterReveal G u) A₀)
        (by
          rw [Exploration.revealRecordEvent_eq_frozenStateEvent
            (clusterReveal G u) (clusterReveal_stable G u) A₀]
          exact frozenStateEvent_support θ ξ (clusterReveal G u A₀)
            (Exploration.revealRecordConfiguration (clusterReveal G u) A₀)) =
      (law G θ ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support θ ξ (subgraphRemovedEdges H G) K') := by
    congr 1
  rw [hfiltered,law_filter_frozen_map_embeddedRestriction]

end
end PottsContinuity.Thm3.Prop4
