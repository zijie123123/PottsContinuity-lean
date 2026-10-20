module

public import PottsContinuity.Thm3.RSW.FrozenEventRestore
public import PottsContinuity.Thm3.RSW.FrozenBoundarySupport
public import PottsContinuity.Thm3.RSW.EmbeddedDecreasingLower
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance frozenPartialEdgeEq {Y : Type*} (H : SimpleGraph Y) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- A partially frozen original law dominates the wired reference on an
embedded decreasing event. Frozen support, residual closure and restoration
of the actual sampled event are specified geometrically. -/
theorem frozen_partial_decreasing_reference_lower_of_closedInterior
    {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (f : X ↪ Y)
    (θ : Parameters) (ξ : BoundaryCondition Y)
    (R : Configuration H) (K : RemovedConfiguration H R) (D : Set Y)
    (hD : ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃v : Y⦄, v ∈ e.val → v ∈ D)
    (hGH : G.map f ≤ edgeRestriction H R) (B : Set X)
    (hclosed : ∀ ⦃x : X⦄, x ∉ B → ∀ ⦃y : Y⦄,
      (edgeRestriction H R).Adj (f x) y → ∃ z : X, f z = y ∧ G.Adj x z)
    (havoid : ∀ ⦃x : X⦄, x ∉ B → f x ∉ ξ.boundary ∪ D)
    (S : Set (Configuration G)) (hS : IsLowerSet S) (E : Set (Configuration H))
    (hevent : ∀ A : Configuration (edgeRestriction H R),
      (edgeRestrictionConfigurationEquiv H R A).val ∪ K.val ∈ E ↔
        embeddedConfigurationRestriction G (edgeRestriction H R) f hGH A ∈ S) :
    (measure G θ (BoundaryCondition.wired B) S).toReal ≤
      (((law H θ ξ).filter (frozenStateEvent R K)
        (frozenStateEvent_support θ ξ R K)).toMeasure E).toReal := by
  rw [frozen_event_probability_eq_restored_remaining]
  have hlaw : remainingLaw H θ (frozenBoundary ξ K.val) R =
      (law (edgeRestriction H R) θ (frozenBoundaryWithSupport ξ K.val D hD)).map
        (edgeRestrictionConfigurationEquiv H R) := by
    have hboundary : law (edgeRestriction H R) θ (frozenBoundaryWithSupport ξ K.val D hD) =
        law (edgeRestriction H R) θ (frozenBoundary ξ K.val) :=
      law_eq_of_boundary_partition_eq θ _ _ rfl
    rw [hboundary]
    exact (law_edgeRestriction_map H θ (frozenBoundary ξ K.val) R).symm
  rw [hlaw,PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top]
  have hset : (edgeRestrictionConfigurationEquiv H R) ⁻¹' {A | A.val ∪ K.val ∈ E} =
      {A | embeddedConfigurationRestriction G (edgeRestriction H R) f hGH A ∈ S} := by
    ext A
    exact hevent A
  rw [hset]
  exact embedded_decreasing_reference_lower_of_closedInterior G (edgeRestriction H R)
    f hGH θ (frozenBoundaryWithSupport ξ K.val D hD) B hclosed havoid S hS

end
end PottsContinuity.RSW
