module

public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- A decreasing event in a closed embedded interior has at least its wired
reference probability. All closure and original boundary avoidance is literal. -/
theorem embedded_decreasing_reference_lower_of_closedInterior
    {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (f : X ↪ Y) (hGH : G.map f ≤ H)
    (θ : Parameters) (ξ : BoundaryCondition Y) (B : Set X)
    (hclosed : ∀ ⦃x : X⦄, x ∉ B → ∀ ⦃y : Y⦄, H.Adj (f x) y →
      ∃ z : X, f z = y ∧ G.Adj x z)
    (havoid : ∀ ⦃x : X⦄, x ∉ B → f x ∉ ξ.boundary)
    (S : Set (Configuration G)) (hS : IsLowerSet S) :
    (measure G θ (BoundaryCondition.wired B) S).toReal ≤
      (measure H θ ξ {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  have h := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ ξ B hclosed havoid Sᶜ hS.compl
  change (measure H θ ξ).real ({A | embeddedConfigurationRestriction G H f hGH A ∈ S}ᶜ) ≤
    (measure G θ (BoundaryCondition.wired B)).real Sᶜ at h
  rw [probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top,
    probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top] at h
  change (measure G θ (BoundaryCondition.wired B)).real S ≤
    (measure H θ ξ).real {A | embeddedConfigurationRestriction G H f hGH A ∈ S}
  linarith only [h]

end
end PottsContinuity.RSW
