module

public import PottsContinuity.PD.FK.Model

/-! # Exact residual-law identities transfer event lower bounds -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- An exact pushforward law and supportwise event transport transfer a lower
bound. The hypothesis is a complete law identity, not a numerical event bound. -/
theorem residual_event_lower_of_residualLaw
    {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y)
    (ρ : PMF (Configuration G)) (θ : Parameters) (ξ : BoundaryCondition Y)
    (read : Configuration G → Configuration H)
    (hlaw : ρ.map read = law H θ ξ)
    (S : Set (Configuration H)) (F : Set (Configuration G))
    (htransport : ∀ A ∈ ρ.support, read A ∈ S → A ∈ F) :
    (measure H θ ξ S).toReal ≤ (ρ.toMeasure F).toReal := by
  have hmass := congrArg (fun p : PMF (Configuration H) => p.toMeasure S) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at hmass
  have hsub : ρ.toMeasure (read ⁻¹' S) ≤ ρ.toMeasure F := by
    apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
    intro A hA
    exact htransport A hA.2 hA.1
  unfold PD.FK.measure
  rw [← hmass]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hsub

end
end PottsContinuity.RSW
