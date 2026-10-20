-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/ConditionalEmbeddedBoundaryUpper.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/ConditionalEmbeddedBoundaryUpper.lean`.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PD.FK

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
    (q : Parameters) (ξ : BoundaryCondition W)
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
end PottsContinuity.PD.FK
