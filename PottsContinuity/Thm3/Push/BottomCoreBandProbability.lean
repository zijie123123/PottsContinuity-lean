module

public import PottsContinuity.Thm3.Push.BottomCoreBandTransfer
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PD.Duality PlanarMixed.Square MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Actual core band crossing probability dominates the ordinary-rectangle
band probability for every admissible FK parameter. Both the path transfer
and free-leaf/boundary marginal law have been proved; no core comparison is
assumed as an input. -/
theorem bottomCoreBand_probability_ge_rectangleBand
    (θ : Parameters) (a : LatticeVertex) (w h b : ℕ) (hw : 1 ≤ w) (hbh : b < h) :
    (measure (rectangleGraph (a.1-1,a.2) (w+1) h) θ
      (BoundaryCondition.wired {z : RectangleVertex (a.1-1,a.2) (w+1) h |
        z.val.1 = a.1-1 ∨ z.val.1 = a.1+(w:ℤ) ∨ z.val.2 = a.2+(h:ℤ)})
      (rectangleBandConnectionEvent (a.1-1,a.2) (w+1) b h hbh.le)).toReal ≤
    (measure (generalRectangleDualBottomCoreGraph a w h) θ
      (BoundaryCondition.wired {u : generalRectangleDualBottomCoreVertex a w h |
        bottomCoreInclusion a w h u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h})
      (bottomCoreBandEvent a w h b)).toReal := by
  let ρ := embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
    (rectangleGraph (a.1-1,a.2) (w+1) h)
    (generalRectangleDualBottomCoreVertexEquiv a w h).toEmbedding (bottomCoreAmbient_map_le a w h)
  have hid := congrArg (fun μ => (PMF.toMeasure μ (bottomCoreBandEvent a w h b)).toReal)
    (bottomCoreAmbient_law_restrict a w h θ)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hid
  change (measure (rectangleGraph (a.1-1,a.2) (w+1) h) θ
      (BoundaryCondition.wired {z : RectangleVertex (a.1-1,a.2) (w+1) h |
        z.val.1 = a.1-1 ∨ z.val.1 = a.1+(w:ℤ) ∨ z.val.2 = a.2+(h:ℤ)})
      (ρ ⁻¹' bottomCoreBandEvent a w h b)).toReal = _ at hid
  simp only [PD.FK.measure] at hid ⊢
  rw [← hid]
  have hsub : rectangleBandConnectionEvent (a.1-1,a.2) (w+1) b h hbh.le ⊆
      ρ ⁻¹' bottomCoreBandEvent a w h b := by
    intro C hC
    exact bottomCoreBandEvent_of_rectangle_band a w h b hw hbh C hC
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

end
end PottsContinuity.Push
