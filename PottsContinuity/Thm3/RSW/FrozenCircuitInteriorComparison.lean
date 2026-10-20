module

public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.PD.RCInfinite.SubgraphComparison
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance frozenCircuitComparisonEdgeEq {X : Type*} (G : SimpleGraph X) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance frozenCircuitComparisonEdgeFintype {X : Type*} [Finite X] (G : SimpleGraph X) :
    Fintype G.edgeSet := Fintype.ofFinite _

/-- A frozen circuit partition dominates an ambient reference law on every
increasing inner event. The inner graph may omit observed circuit edges;
only vertices away from the designated circuit boundary must be closed under
ambient adjacency and avoid the reference boundary. -/
theorem frozen_reference_lower_of_wiredCircuitPartition
    {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (f : X ↪ Y) (hGH : G.map f ≤ H)
    (θ : Parameters) (ξ η : BoundaryCondition Y) (B : Set X)
    (hclosed : ∀ ⦃x : X⦄, x ∉ B → ∀ ⦃y : Y⦄, H.Adj (f x) y →
      ∃ z : X, f z = y ∧ G.Adj x z)
    (havoid : ∀ ⦃x : X⦄, x ∉ B → f x ∉ η.boundary)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (hwire : (BoundaryCondition.wired B).partition ≤
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure H θ η {A | embeddedConfigurationRestriction G H f hGH A ∈ E}).toReal ≤
    (((law H θ ξ).filter (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support θ ξ _ K)).toMeasure
      {A | embeddedConfigurationRestriction G H f hGH A ∈ E}).toReal := by
  have hdom := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ η B hclosed havoid E hE
  have hbc := measure_boundary_comparison θ (BoundaryCondition.wired B)
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) hwire E hE
  have hlaw := law_filter_frozen_map_embeddedRestriction G H f hGH θ ξ K
  have hprob := congrArg (fun p : PMF (Configuration G) => (p.toMeasure E).toReal) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hprob
  exact (hdom.trans hbc).trans_eq hprob.symm

end
end PottsContinuity.RSW
