module

public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration MeasureTheory RSW
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourceRecordAverageEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Bounds on every attained record of an event average without requiring
that the event itself be observable. Records meeting the event are selected
by their actual image, which may have a larger probability than the event. -/
theorem stopped_event_lower_of_bounds_on_event
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (reveal : RevealMap (G := G))
    (hstable : ∀ C D, D ∩ reveal C = C ∩ reveal C → reveal D = reveal C)
    (A E : Set (Configuration G)) (c : ℝ) (hc : 0 ≤ c)
    (hrecord : ∀ C ∈ E,
      c ≤ (((law G θ ξ).filter (revealRecordEvent reveal C) (by
        rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C]
        exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure A).toReal) :
    c * (measure G θ ξ E).toReal ≤ (measure G θ ξ A).toReal := by
  let T := stoppingObservationMap reveal '' E
  have hb := stopped_event_lower_of_record_bounds θ ξ reveal hstable A T c (by
    intro C hC
    obtain ⟨C₀,hC₀,heq⟩ := hC
    have hset : revealRecordEvent reveal C₀ = revealRecordEvent reveal C := by
      rw [← stoppingObservationMap_fiber reveal C₀,← stoppingObservationMap_fiber reveal C,heq]
    simpa only [hset] using hrecord C₀ hC₀)
  have hE : E ⊆ (stoppingObservationMap reveal) ⁻¹' T := by
    intro C hC
    exact ⟨C,hC,rfl⟩
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hE) hc).trans hb

end
end PottsContinuity.Push
