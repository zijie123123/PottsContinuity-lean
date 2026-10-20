module

public import PottsContinuity.PlanarTopology.RectangleLocalGluing

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

theorem probability_inter_two_lower (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (A B : Set LatticeConfiguration) (hB : MeasurableSet B) :
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have he := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hu : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

theorem probability_inter_three_lower (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (A B C : Set LatticeConfiguration) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    μ.real A + μ.real B + μ.real C - 2 ≤ μ.real ((A ∩ B) ∩ C) := by
  have h₁ := probability_inter_two_lower μ A B hB
  have h₂ := probability_inter_two_lower μ (A ∩ B) C hC
  linarith

/-- Quantitative transfer of one seed-side connection to an infinite marked
root, losing only the probabilities of the two failed input events. -/
theorem rectangle_connection_transfer_probability_lower
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (a : LatticeVertex) (w h : ℕ) (A C B : Set LatticeVertex) (S T : Finset LatticeVertex)
    (hA : A ⊆ (S : Set LatticeVertex)) (hC : C ⊆ (S : Set LatticeVertex))
    (hCR : C ⊆ (PD.FK.latticeRectangle a w h : Set LatticeVertex))
    (hTR : (T : Set LatticeVertex) ⊆ (PD.FK.latticeRectangle a w h : Set LatticeVertex))
    (hBT : ∀ z ∈ B, z ∉ T) :
    μ.real (infiniteHit C) + μ.real (rectangleConnectionEvent a w h A B) +
      μ.real (finiteLocalUniquenessEvent S T) - 2 ≤
      μ.real (rectangleConnectionEvent a w h C B) := by
  have hs : (infiniteHit C ∩ rectangleConnectionEvent a w h A B) ∩
      finiteLocalUniquenessEvent S T ⊆ rectangleConnectionEvent a w h C B := by
    rintro ω ⟨⟨hi,hc⟩,hl⟩
    exact rectangleConnectionEvent_transfer_of_finiteLocalUniqueness a w h A C B S T
      hA hC hCR hTR hBT ω hl hi hc
  exact (probability_inter_three_lower μ _ _ _ (rectangleConnectionEvent_measurableSet _ _ _ _ _)
    (finiteLocalUniquenessEvent_measurableSet _ _)).trans (measureReal_mono hs)

/-- Quantitative two-path gluing inside a common containing rectangle, without
requiring the finite local-uniqueness event to be increasing. -/
theorem rectangle_connection_glue_probability_lower
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (a a₁ a₂ : LatticeVertex) (w h w₁ h₁ w₂ h₂ : ℕ)
    (A B L U : Set LatticeVertex) (S T : Finset LatticeVertex)
    (hD₁ : (PD.FK.latticeRectangle a₁ w₁ h₁ : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hD₂ : (PD.FK.latticeRectangle a₂ w₂ h₂ : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hTD : (T : Set LatticeVertex) ⊆ PD.FK.latticeRectangle a w h)
    (hA : A ⊆ (S : Set LatticeVertex)) (hB : B ⊆ (S : Set LatticeVertex))
    (hLT : ∀ z ∈ L, z ∉ T) (hUT : ∀ z ∈ U, z ∉ T) :
    μ.real (rectangleConnectionEvent a₁ w₁ h₁ A L) +
      μ.real (rectangleConnectionEvent a₂ w₂ h₂ B U) + μ.real (finiteLocalUniquenessEvent S T) - 2 ≤
      μ.real (rectangleConnectionEvent a w h L U) := by
  have hs : (rectangleConnectionEvent a₁ w₁ h₁ A L ∩ rectangleConnectionEvent a₂ w₂ h₂ B U) ∩
      finiteLocalUniquenessEvent S T ⊆ rectangleConnectionEvent a w h L U := by
    rintro ω ⟨⟨hfirst,hsecond⟩,hl⟩
    exact rectangleConnectionEvent_glue_of_finiteLocalUniqueness a a₁ a₂ w h w₁ h₁ w₂ h₂
      A B L U S T hD₁ hD₂ hTD hA hB hLT hUT ω hl hfirst hsecond
  exact (probability_inter_three_lower μ _ _ _ (rectangleConnectionEvent_measurableSet _ _ _ _ _)
    (finiteLocalUniquenessEvent_measurableSet _ _)).trans (measureReal_mono hs)

end
end PottsContinuity.PlanarTopology
