module

public import PottsContinuity.Thm3.Prop4.FrozenFiberDualArms
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Decreasing events in the full restored conditional sample

The exact deleted-graph law correlates arbitrary original lower events after
restoring the fixed revealed state. No additional primal event is conditioned.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance frozenCorrelationOriginalDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- Two original lower events are positively correlated under each exact
normalized frozen-state law, including the restored revealed edges. -/
theorem frozen_fiber_lower_events_correlation (V : Finset LatticeVertex)
    (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (B : RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R)
    (E F : Set (Configuration (squareLattice.induce (V : Set LatticeVertex))))
    (hE : IsLowerSet E) (hF : IsLowerSet F) :
    ((frozenFiberLaw θ ξ R B).toMeasure {A | A.val ∪ B.val ∈ E}).toReal *
    ((frozenFiberLaw θ ξ R B).toMeasure {A | A.val ∪ B.val ∈ F}).toReal ≤
    ((frozenFiberLaw θ ξ R B).toMeasure {A | A.val ∪ B.val ∈ E ∩ F}).toReal := by
  rw [frozen_fiber_event_probability_eq_deleted,frozen_fiber_event_probability_eq_deleted,
    frozen_fiber_event_probability_eq_deleted,Set.preimage_inter]
  apply finite_FK_lower_event_correlation
  · intro A C hCA hA
    exact hE (Finset.union_subset_union
      ((edgeRestrictionConfigurationOrderIso _ R).monotone hCA) le_rfl) hA
  · intro A C hCA hA
    exact hF (Finset.union_subset_union
      ((edgeRestrictionConfigurationOrderIso _ R).monotone hCA) le_rfl) hA

end
end PottsContinuity.Thm3.Prop4
