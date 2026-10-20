module

public import PottsContinuity.PlanarTopology.RectangleTranspose
public import PottsContinuity.PlanarTopology.DRTHorizontalFixedWidth

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
open scoped ENNReal
noncomputable section

/-- Every fixed positive-height vertical crossing tends to probability one
as width grows; the original law need not have coordinate-interchange symmetry. -/
theorem verticalRectangle_fixed_height_real_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) (h : ℕ) :
    Tendsto (fun n : ℕ => μ.real (verticalRectangle (0,0) n (h+1))) atTop (𝓝 1) := by
  have hh := horizontalRectangle_fixed_width_real_probability_tendsto_one
    (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso))
    (transposeLaw_translation_invariant μ htranslation) (transposeLaw_FKG μ hFKG)
    (configurationIsoLaw_unique latticeTransposeIso μ hunique)
    (configurationIsoLaw_infinite latticeTransposeIso μ hinfinite) h
  have heq (n : ℕ) :
      (μ.map (latticeConfigurationIsoHomeomorph latticeTransposeIso)).real
        (horizontalRectangle (0,0) (h+1) n) = μ.real (verticalRectangle (0,0) n (h+1)) := by
    have ht := transposeLaw_horizontalRectangle μ (0,0) n (h+1)
    simpa only [Prod.swap,Measure.real_def] using congrArg ENNReal.toReal ht
  simpa only [heq] using hh

theorem horizontalRectangle_fixed_height_real_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) (K : ℕ) :
    Tendsto (fun n : ℕ => μ.real (horizontalRectangle (0,0) (n+1) K)) atTop (𝓝 0) := by
  have hh := ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
    (horizontalRectangle_fixed_height_probability_tendsto_zero μ htranslation hFKG hunique hinfinite K)
  simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_zero] using hh

theorem verticalRectangle_fixed_width_real_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent) (W : ℕ) :
    Tendsto (fun n : ℕ => μ.real (verticalRectangle (0,0) W (n+1))) atTop (𝓝 0) := by
  have hh := ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
    (verticalRectangle_fixed_width_probability_tendsto_zero μ htranslation hFKG hunique hinfinite W)
  simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_zero] using hh

end
end PottsContinuity.PlanarTopology
