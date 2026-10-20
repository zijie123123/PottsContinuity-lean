module

public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Actual decreasing events are positively associated under every finite
FK law and every boundary partition. -/
theorem finite_decreasing_positive_association
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (S T : Set (Configuration G))
    (hS : IsLowerSet S) (hT : IsLowerSet T) :
    (measure G θ ξ S).toReal * (measure G θ ξ T).toReal ≤
      (measure G θ ξ (S ∩ T)).toReal := by
  have h := measure_positive_association (G := G) θ ξ Sᶜ Tᶜ hS.compl hT.compl
  change (measure G θ ξ).real Sᶜ * (measure G θ ξ).real Tᶜ ≤
    (measure G θ ξ).real (Sᶜ ∩ Tᶜ) at h
  rw [← Set.compl_union,probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top] at h
  have hu := measureReal_union_add_inter (μ := measure G θ ξ) (s := S) (t := T)
    MeasurableSpace.measurableSet_top (measure_ne_top _ _) (measure_ne_top _ _)
  change (measure G θ ξ).real S * (measure G θ ξ).real T ≤
    (measure G θ ξ).real (S ∩ T)
  nlinarith only [h,hu]

end
end PottsContinuity.RSW
