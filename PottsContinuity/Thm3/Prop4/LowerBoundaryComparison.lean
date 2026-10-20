module

public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Decreasing events under boundary wiring

Complementation transports the finite FK boundary comparison to lower events.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Adding boundary identifications decreases every actual lower-event probability. -/
theorem finite_FK_lower_boundary_comparison {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ η : BoundaryCondition V) (hξη : ξ.partition ≤ η.partition)
    (E : Set (Configuration G)) (hE : IsLowerSet E) :
    (measure G θ η E).toReal ≤ (measure G θ ξ E).toReal := by
  have h := measure_boundary_comparison (G := G) θ ξ η hξη Eᶜ hE.compl
  change (measure G θ ξ).real Eᶜ ≤ (measure G θ η).real Eᶜ at h
  rw [probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top] at h
  change (measure G θ η).real E ≤ (measure G θ ξ).real E
  linarith only [h]

end
end PottsContinuity.Thm3.Prop4
