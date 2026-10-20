-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/PMFDiscreteMeasureInstanceIrrel.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- A finite PMF evaluates every event identically under any two discrete
measurable-space instances on the same carrier. -/
theorem pmf_toMeasure_apply_eq_of_discrete_instances
    {α : Type*} [Fintype α] (p : PMF α) (E : Set α)
    (m₁ m₂ : MeasurableSpace α)
    (d₁ : @DiscreteMeasurableSpace α m₁)
    (d₂ : @DiscreteMeasurableSpace α m₂) :
    @PMF.toMeasure α m₁ p E = @PMF.toMeasure α m₂ p E := by
  have h₁ : @PMF.toMeasure α m₁ p E = ∑ a : α, E.indicator p a := by
    let : MeasurableSpace α := m₁
    let : DiscreteMeasurableSpace α := d₁
    exact PMF.toMeasure_apply_fintype p E
  have h₂ : @PMF.toMeasure α m₂ p E = ∑ a : α, E.indicator p a := by
    let : MeasurableSpace α := m₂
    let : DiscreteMeasurableSpace α := d₂
    exact PMF.toMeasure_apply_fintype p E
  rw [h₁, h₂]

/-- The corresponding real-valued probabilities are independent of the
chosen discrete measurable-space instance as well. -/
theorem pmf_toMeasure_apply_toReal_eq_of_discrete_instances
    {α : Type*} [Fintype α] (p : PMF α) (E : Set α)
    (m₁ m₂ : MeasurableSpace α)
    (d₁ : @DiscreteMeasurableSpace α m₁)
    (d₂ : @DiscreteMeasurableSpace α m₂) :
    (@PMF.toMeasure α m₁ p E).toReal = (@PMF.toMeasure α m₂ p E).toReal := by
  rw [pmf_toMeasure_apply_eq_of_discrete_instances p E m₁ m₂ d₁ d₂]

end PottsContinuity.FKC.FiniteFK

