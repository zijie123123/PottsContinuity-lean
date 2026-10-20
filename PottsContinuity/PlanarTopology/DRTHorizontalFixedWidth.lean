module

public import PottsContinuity.PlanarTopology.DRTFixedSideDecay
public import PottsContinuity.PlanarTopology.RectangleEventTranslation
public import PottsContinuity.BD12.WholePlaneRectangleDuality

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
open scoped ENNReal
noncomputable section

/-- At every fixed positive width, the actual horizontal crossing probability
tends to one as height grows. Only original unique existing infinity is used. -/
theorem horizontalRectangle_fixed_width_real_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω)
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) (w : ℕ) :
    Tendsto (fun n : ℕ => μ.real (horizontalRectangle (0,0) (w+1) n)) atTop (𝓝 1) := by
  let ν := μ.map wholePlaneDualConfigurationHomeomorph
  have hνν : ν.map wholePlaneDualConfigurationHomeomorph = μ := wholePlaneDualLaw_twice μ htranslation
  have htrans : ∀ a : LatticeVertex, ν.map (edgeTranslate a) = ν :=
    wholePlaneDualLaw_translation_invariant μ htranslation
  have hu : ∀ᵐ η ∂ν, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph η) := by
    apply (wholePlaneDualLaw_ae_iff ν _).mp
    rwa [hνν]
  have hi : ∀ᵐ η ∂ν, wholePlaneDualConfigurationHomeomorph η ∈ infiniteClusterEvent := by
    apply (wholePlaneDualLaw_ae_iff ν _).mp
    rwa [hνν]
  have hbound (n : ℕ) : μ ((horizontalRectangle (0,0) (w+1) n)ᶜ) ≤
      ν (verticalRectangle (0,0) w (n+1)) := by
    rw [horizontalRectangle_compl]
    rw [← Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
      (dualPortRectangle_isCylinder _ _ _).measurableSet]
    have ht : ν (verticalRectangle (0,-1) w (n+1)) = ν (verticalRectangle (0,0) w (n+1)) := by
      simpa only [latticeTranslate,Prod.fst_zero,Prod.snd_zero,zero_add] using
        measure_verticalRectangle_translate ν (0,-1) (0,0) (htrans _) w (n+1)
    exact (measure_mono (dualPortRectangle_subset_vertical (0,0) w n)).trans_eq ht
  have hcomp : Tendsto (fun n : ℕ => μ ((horizontalRectangle (0,0) (w+1) n)ᶜ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (verticalRectangle_fixed_width_probability_tendsto_zero ν htrans (wholePlaneDualLaw_FKG μ hFKG) hu hi w)
      (fun _ => zero_le) hbound
  have hcompR : Tendsto (fun n : ℕ => μ.real ((horizontalRectangle (0,0) (w+1) n)ᶜ)) atTop (𝓝 0) := by
    have hh := ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp hcomp
    simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_zero] using hh
  have heq (n : ℕ) : μ.real (horizontalRectangle (0,0) (w+1) n) =
      1-μ.real ((horizontalRectangle (0,0) (w+1) n)ᶜ) := by
    have hh := measureReal_compl (μ := μ) (horizontalRectangle_isCylinder (0,0) (w+1) n).measurableSet
    have hone : μ.real Set.univ = 1 := by simp [Measure.real_def]
    rw [hone] at hh
    linarith
  simpa only [← heq,sub_zero] using (tendsto_const_nhds.sub hcompR :
    Tendsto (fun n : ℕ => 1-μ.real ((horizontalRectangle (0,0) (w+1) n)ᶜ)) atTop (𝓝 (1-(0:ℝ))))

end
end PottsContinuity.PlanarTopology
