module

public import PottsContinuity.Thm3.RSW.FiniteDecreasingAssociation
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- Remaining-edge decreasing events are positively associated, for arbitrary
removed bonds, interior parameters and boundary partitions. -/
theorem remaining_decreasing_positive_association
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G)
    (S T : Set (RemainingConfiguration G R)) (hS : IsLowerSet S) (hT : IsLowerSet T) :
    ((remainingLaw G θ ξ R).toMeasure S).toReal *
      ((remainingLaw G θ ξ R).toMeasure T).toReal ≤
        ((remainingLaw G θ ξ R).toMeasure (S ∩ T)).toReal := by
  let e := edgeRestrictionConfigurationEquiv G R
  have heq (D : Set (RemainingConfiguration G R)) :
      (remainingLaw G θ ξ R).toMeasure D =
        measure (edgeRestriction G R) θ ξ (e ⁻¹' D) := by
    rw [← law_edgeRestriction_map]
    exact PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top
  rw [heq S,heq T,heq (S ∩ T),Set.preimage_inter]
  apply finite_decreasing_positive_association
  · intro A B hAB hB
    exact hS ((edgeRestrictionConfigurationOrderIso G R).monotone hAB) hB
  · intro A B hAB hB
    exact hT ((edgeRestrictionConfigurationOrderIso G R).monotone hAB) hB

end
end PottsContinuity.RSW
