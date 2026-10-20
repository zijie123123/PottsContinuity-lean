module

public import PottsContinuity.Thm3.Push.IntervalArmRecordLowerBound
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12 PottsContinuity.Exploration
noncomputable section
local instance armPairConnectionEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- Finite-box Case 1 of Lemma 2: actual simultaneous interval-to-top arms
produce an actual connection of the ORIGINAL source intervals, with the mixed
square factor. This holds for every original boundary and every real q>=1,
at the explicit self-dual parameter, with no exploration premise. -/
theorem intervalArmPair_connection_probability_ge
    (q : Set.Ici (1 : ℝ)) (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂) (ξ : BoundaryCondition (RectangleVertex (0,0) N N)) :
    (1 / (1 + (q : ℝ)^2)) *
      (measure (rectangleGraph (0,0) N N) (criticalParameters q) ξ
        (intervalArmPairEvent N l₁ r₁ l₂ r₂)).toReal ≤
      (measure (rectangleGraph (0,0) N N) (criticalParameters q) ξ
        (arcsConnectionEvent (rectangleGraph (0,0) N N)
          (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))).toReal := by
  have hpre := intervalArmPair_success_observation_preimage N l₁ r₁ l₂ r₂
    hl₁ h₁ hr₁ hl₂ h₂ hr₂
  have h := RSW.stopped_event_lower_of_record_bounds (criticalParameters q) ξ
    (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂)
    (intervalArmJointFilledReveal_stable N l₁ r₁ l₂ r₂)
    (arcsConnectionEvent (rectangleGraph (0,0) N N)
      (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂))
    (selectedRevealObservations (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂)
      (intervalArmPairEvent N l₁ r₁ l₂ r₂)) (1/(1+(q : ℝ)^2)) (by
        intro A hselected
        have hA : A ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂ := by
          rw [← hpre]
          exact hselected
        exact intervalArmPair_record_connection_lower_bound q N hN l₁ r₁ l₂ r₂
          hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder ξ A hA)
  simpa only [hpre] using h

end
end PottsContinuity.Push
