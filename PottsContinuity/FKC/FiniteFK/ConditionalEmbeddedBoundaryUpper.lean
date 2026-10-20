-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ConditionalEmbeddedBoundaryUpper.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance innerConfigurationMeasurableSpace :
    MeasurableSpace (Configuration G) := ⊤
local instance outerConfigurationMeasurableSpace :
    MeasurableSpace (Configuration H) := ⊤

/-- For an exact outside-edge state, the actual filtered outer FK law restricted
to the embedded inner graph is bounded above by any boundary law that dominates
the induced frozen boundary. -/
theorem filteredConditionalEmbeddedEvent_measure_le_boundary
    (q : ClusterWeight) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (η : BoundaryCondition V)
    (hpart :
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
        η.partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (PMF.toMeasure (((law H q ξ).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support q ξ (subgraphRemovedEdges (G.map f) H) K)).map
        (embeddedConfigurationRestriction G H f hGH)) S).toReal ≤
      (measure G q η S).toReal := by
  have hconditional := law_filter_frozen_map_embeddedRestriction
    G H f hGH q ξ K
  have hmeasure :
      (PMF.toMeasure (((law H q ξ).filter
        (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
        (frozenStateEvent_support q ξ (subgraphRemovedEdges (G.map f) H) K)).map
          (embeddedConfigurationRestriction G H f hGH)) S).toReal =
        (measure G q
          (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S).toReal := by
    simpa [measure] using congrArg
      (fun μ : PMF (Configuration G) => (μ.toMeasure S).toReal) hconditional
  rw [hmeasure]
  exact measure_boundary_comparison q
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) η hpart S hS

end
end PottsContinuity.FKC.FiniteFK
