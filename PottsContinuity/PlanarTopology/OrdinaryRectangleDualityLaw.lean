module

public import PottsContinuity.PlanarTopology.OrdinaryRectangleDuality
public import PottsContinuity.PlanarTopology.DualRoleExchange
public import PottsContinuity.PlanarTopology.RectangleEventTranslation

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12
noncomputable section

/-- Exact dual vertical strip probability after translation removes its lower
face-base offset. No symmetry or infinite-cluster premise is needed. -/
theorem dualLaw_verticalRectangle_eq_one_sub_horizontal
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) (n h : ℕ) :
    (μ.map wholePlaneDualConfigurationHomeomorph).real (verticalRectangle (0,0) n (h+1)) =
      1-μ.real (horizontalRectangle (0,0) (n+1) h) := by
  let ν := μ.map wholePlaneDualConfigurationHomeomorph
  have ht : ν (verticalRectangle (0,-1) n (h+1)) = ν (verticalRectangle (0,0) n (h+1)) := by
    simpa only [latticeTranslate,Prod.fst_zero,Prod.snd_zero,zero_add] using
      measure_verticalRectangle_translate ν (0,-1) (0,0)
        (wholePlaneDualLaw_translation_invariant μ htranslation _) n (h+1)
  have heq : ν (verticalRectangle (0,-1) n (h+1)) = μ ((horizontalRectangle (0,0) (n+1) h)ᶜ) := by
    rw [Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
      (verticalRectangle_isCylinder _ _ _).measurableSet]
    congr 1
    exact (horizontalRectangle_compl_eq_dual_vertical (0,0) n h).symm
  have hr := congrArg ENNReal.toReal (ht.symm.trans heq)
  have hc := measureReal_compl (μ := μ) (horizontalRectangle_isCylinder (0,0) (n+1) h).measurableSet
  have hu : μ.real Set.univ = 1 := by simp [Measure.real_def]
  rw [hu] at hc
  simp only [Measure.real_def] at hc
  rw [hc] at hr
  exact hr

/-- The transposed dual horizontal strip uses width w+1 and height n for an
original vertical rectangle of width w and height n+1. -/
theorem dualLaw_horizontalRectangle_eq_one_sub_vertical
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) (w n : ℕ) :
    (μ.map wholePlaneDualConfigurationHomeomorph).real (horizontalRectangle (0,0) (w+1) n) =
      1-μ.real (verticalRectangle (0,0) w (n+1)) := by
  let ν := μ.map wholePlaneDualConfigurationHomeomorph
  have ht : ν (horizontalRectangle (-1,0) (w+1) n) = ν (horizontalRectangle (0,0) (w+1) n) := by
    simpa only [latticeTranslate,Prod.fst_zero,Prod.snd_zero,zero_add] using
      measure_horizontalRectangle_translate ν (-1,0) (0,0)
        (wholePlaneDualLaw_translation_invariant μ htranslation _) (w+1) n
  have heq : ν (horizontalRectangle (-1,0) (w+1) n) = μ ((verticalRectangle (0,0) w (n+1))ᶜ) := by
    rw [Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
      (horizontalRectangle_isCylinder _ _ _).measurableSet]
    congr 1
    exact (verticalRectangle_compl_eq_dual_horizontal (0,0) w n).symm
  have hr := congrArg ENNReal.toReal (ht.symm.trans heq)
  have hc := measureReal_compl (μ := μ) (verticalRectangle_isCylinder (0,0) w (n+1)).measurableSet
  have hu : μ.real Set.univ = 1 := by simp [Measure.real_def]
  rw [hu] at hc
  simp only [Measure.real_def] at hc
  rw [hc] at hr
  exact hr

end
end PottsContinuity.PlanarTopology
