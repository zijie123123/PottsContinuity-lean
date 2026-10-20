module

public import PottsContinuity.PD.FK.FrozenLimitBridge
public import PottsContinuity.PD.Duality.WholePlaneDualGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Actual dual-arm correlation in a fresh finite FK law

The two events have a common agreeing extension by the proved meet construction.
This finite-law inequality does not assert positive association after an
additional primal-connection conditioning.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Actual finite FK lower events are positively correlated before further conditioning. -/
theorem finite_FK_lower_event_correlation {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ : BoundaryCondition V) (A B : Set (Configuration G))
    (hA : IsLowerSet A) (hB : IsLowerSet B) :
    (measure G θ ξ A).toReal*(measure G θ ξ B).toReal ≤ (measure G θ ξ (A ∩ B)).toReal := by
  let ν := measure G θ ξ
  have h := measure_positive_association (G := G) θ ξ Aᶜ Bᶜ hA.compl hB.compl
  change ν.real Aᶜ*ν.real Bᶜ ≤ ν.real (Aᶜ ∩ Bᶜ) at h
  rw [← Set.compl_union,probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top] at h
  have hsum := measureReal_union_add_inter (μ := ν) (s := A) (t := B) MeasurableSpace.measurableSet_top
  change ν.real A*ν.real B ≤ ν.real (A ∩ B)
  nlinarith only [h,hsum]

end
end PottsContinuity.Thm3.Prop4
