module

public import PottsContinuity.Thm3.RSW.FrozenEventRestore
public import PottsContinuity.Thm3.RSW.RemainingDecreasingAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance frozenDecreasingEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Conditioning on an exact edge configuration preserves positive
association of decreasing events of the original sampled bonds. -/
theorem frozen_decreasing_positive_association
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G) (K : RemovedConfiguration G R)
    (S T : Set (Configuration G)) (hS : IsLowerSet S) (hT : IsLowerSet T) :
    let Q := (law G θ ξ).filter (frozenStateEvent R K) (frozenStateEvent_support θ ξ R K)
    (Q.toMeasure S).toReal * (Q.toMeasure T).toReal ≤
      (Q.toMeasure (S ∩ T)).toReal := by
  dsimp only
  rw [frozen_event_probability_eq_restored_remaining,
    frozen_event_probability_eq_restored_remaining,
    frozen_event_probability_eq_restored_remaining]
  change ((remainingLaw G θ (frozenBoundary ξ K.val) R).toMeasure
      {A | A.val ∪ K.val ∈ S}).toReal *
    ((remainingLaw G θ (frozenBoundary ξ K.val) R).toMeasure
      {A | A.val ∪ K.val ∈ T}).toReal ≤
    ((remainingLaw G θ (frozenBoundary ξ K.val) R).toMeasure
      ({A | A.val ∪ K.val ∈ S} ∩ {A | A.val ∪ K.val ∈ T})).toReal
  apply remaining_decreasing_positive_association
  · intro A B hAB hB
    exact hS (Finset.union_subset_union hAB (Finset.Subset.refl _)) hB
  · intro A B hAB hB
    exact hT (Finset.union_subset_union hAB (Finset.Subset.refl _)) hB

end
end PottsContinuity.RSW
