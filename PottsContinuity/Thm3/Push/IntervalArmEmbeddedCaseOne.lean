module

public import PottsContinuity.Thm3.Push.IntervalArmPairConnection
public import PottsContinuity.Thm3.Push.EmbeddedLinearEventBound

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.BD12
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The Case-1 pair-to-connection estimate in ANY finite host with its actual
original boundary. All exterior states are integrated by the exact DMP mixture. -/
theorem intervalArmPair_embedded_connection_probability_ge
    {W : Type*} [Finite W] (q : Set.Ici (1 : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂) (H : SimpleGraph W)
    (f : RectangleVertex (0,0) N N ↪ W) (hGH : (rectangleGraph (0,0) N N).map f ≤ H)
    (ξ : BoundaryCondition W) :
    (1/(1+(q : ℝ)^2)) * (measure H (criticalParameters q) ξ
      {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂}).toReal ≤
      (measure H (criticalParameters q) ξ {C | embeddedConfigurationRestriction _ _ f hGH C ∈
        arcsConnectionEvent (rectangleGraph (0,0) N N)
          (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)}).toReal := by
  exact embedded_linear_event_bound_of_all_boundaries _ H f hGH (criticalParameters q) ξ _ _ _
    (fun η => intervalArmPair_connection_probability_ge q N hN l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder η)

/-- The two actual host arm marginals give the Case-1 product estimate;
positive association is applied to the genuine HOST law, after disintegration. -/
theorem intervalArmPair_embedded_connection_probability_ge_product
    {W : Type*} [Finite W] (q : Set.Ici (1 : ℝ))
    (N : ℕ) (hN : 1 ≤ N) (l₁ r₁ l₂ r₂ : ℤ)
    (hl₁ : 0 < l₁) (h₁ : l₁ ≤ r₁) (hr₁ : r₁ < (N : ℤ))
    (hl₂ : 0 < l₂) (h₂ : l₂ ≤ r₂) (hr₂ : r₂ < (N : ℤ))
    (horder : r₁ < l₂) (H : SimpleGraph W)
    (f : RectangleVertex (0,0) N N ↪ W) (hGH : (rectangleGraph (0,0) N N).map f ≤ H)
    (ξ : BoundaryCondition W) :
    ((measure H (criticalParameters q) ξ
      {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmEvent N l₁ r₁}).toReal *
      (measure H (criticalParameters q) ξ
        {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmEvent N l₂ r₂}).toReal) /
          (1+(q : ℝ)^2) ≤
      (measure H (criticalParameters q) ξ {C | embeddedConfigurationRestriction _ _ f hGH C ∈
        arcsConnectionEvent (rectangleGraph (0,0) N N)
          (intervalArmBottomArc N l₁ r₁) (intervalArmBottomArc N l₂ r₂)}).toReal := by
  have hupper : ∀ l r : ℤ, IsUpperSet
      {C | embeddedConfigurationRestriction (rectangleGraph (0,0) N N) H f hGH C ∈ intervalArmEvent N l r} := by
    intro l r C D hCD hC
    exact arcsConnectionEvent_isUpperSet _ _
      (embeddedConfigurationRestriction_monotone _ _ f hGH hCD) hC
  have hfkg := measure_positive_association (criticalParameters q) ξ _ _
    (hupper l₁ r₁) (hupper l₂ r₂)
  calc
    _ = (1/(1+(q : ℝ)^2)) *
        ((measure H (criticalParameters q) ξ
          {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmEvent N l₁ r₁}).toReal *
          (measure H (criticalParameters q) ξ
            {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmEvent N l₂ r₂}).toReal) := by ring
    _ ≤ (1/(1+(q : ℝ)^2)) * (measure H (criticalParameters q) ξ
        {C | embeddedConfigurationRestriction _ _ f hGH C ∈ intervalArmPairEvent N l₁ r₁ l₂ r₂}).toReal :=
      mul_le_mul_of_nonneg_left hfkg (by positivity)
    _ ≤ _ := intervalArmPair_embedded_connection_probability_ge q N hN l₁ r₁ l₂ r₂
      hl₁ h₁ hr₁ hl₂ h₂ hr₂ horder H f hGH ξ

end
end PottsContinuity.Push
