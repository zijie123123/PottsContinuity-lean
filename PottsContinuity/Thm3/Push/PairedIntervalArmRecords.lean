module

public import PottsContinuity.Thm3.Push.IntervalArmRightFrontier

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance jointArmEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
local instance jointArmRemainingFintype (N : ℕ) (R : Configuration (rectangleGraph (0,0) N N)) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) N N) R) := Fintype.ofFinite _

/-- The ACTUAL left exploration from the first interval and right exploration
from the second interval, recorded in one original square configuration. -/
abbrev intervalArmJointFilledReveal (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ) :=
  jointReveal (intervalArmFilledLeftReveal N l₁ r₁) (intervalArmFilledRightReveal N l₂ r₂)

/-- Simultaneous source success, with the original intervals preserved. -/
abbrev intervalArmPairEvent (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ) :=
  intervalArmEvent N l₁ r₁ ∩ intervalArmEvent N l₂ r₂

/-- The two possibly overlapping original-bond records form a stopping set. -/
theorem intervalArmJointFilledReveal_stable (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A =
      A ∩ intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A) :
    intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ B = intervalArmJointFilledReveal N l₁ r₁ l₂ r₂ A :=
  jointReveal_stable _ _ (intervalArmFilledLeftReveal_stable N l₁ r₁)
    (intervalArmFilledRightReveal_stable N l₂ r₂) A B hstates

/-- Both source-arm occurrences, including their failures, are determined by
this concrete left/right joint record. -/
theorem intervalArmPairEvent_readFromJointFilledReveal
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ)) :
    ReadFromReveal (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂)
      (intervalArmPairEvent N l₁ r₁ l₂ r₂) :=
  readFromReveal_joint_inter _ _ (intervalArmFilledLeftReveal_stable N l₁ r₁)
    (intervalArmFilledRightReveal_stable N l₂ r₂) _ _
    (intervalArmEvent_readFromFilledLeftReveal N l₁ r₁ hl₁ h₁ hr₁)
    (intervalArmEvent_readFromFilledRightReveal N l₂ r₂ hl₂ h₂ hr₂)

/-- The common-observation preimage identity for the actual interval arms. -/
theorem intervalArmPair_success_observation_preimage
    (N : ℕ) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ)) :
    RSW.stoppingObservationMap (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂) ⁻¹'
      selectedRevealObservations (intervalArmJointFilledReveal N l₁ r₁ l₂ r₂)
        (intervalArmPairEvent N l₁ r₁ l₂ r₂) = intervalArmPairEvent N l₁ r₁ l₂ r₂ :=
  preimage_selectedRevealObservations _ _
    (intervalArmPairEvent_readFromJointFilledReveal N l₁ r₁ l₂ r₂ hl₁ h₁ hr₁ hl₂ h₂ hr₂)

end
end PottsContinuity.Push
