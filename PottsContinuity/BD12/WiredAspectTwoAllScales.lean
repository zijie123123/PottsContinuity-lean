module

public import PottsContinuity.BD12.KSTWiredSelfDualUniform
public import PottsContinuity.BD12.KSTScaleInterpolation
public import PottsContinuity.BD12.RectangleTranslation
public import PottsContinuity.BD12.RectangleWidthTruncation
public import PottsContinuity.BD12.RectanglePositive

/-! The actual wired aspect-two crossing bound at every integer height.
Geometric interpolation handles large scales and finite energy handles small ones. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- A positive lower bound for every rectangle of width at most twice its height. -/
theorem wired_selfDual_aspect_two_all_scales_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n w : ℕ, 1 ≤ n → w ≤ 2*n →
      c ≤ μ.real (horizontalRectangle (0,0) w n) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨a,ha,hgeo⟩ := wired_selfDual_aspect_eight_geometric_lower_bound q μ hμ
  let b := μ.real (horizontalRectangle (0,0) 3072 0)
  have hb : 0 < b := infinite_horizontalRectangle_probability_pos (criticalParameters q) 1 μ hμ (0,0) 3072 0
  refine ⟨min a b,lt_min ha hb,fun n w hn hw => ?_⟩
  by_cases hlarge : 1536 ≤ n
  · obtain ⟨j,hheight,hwidth⟩ := kst_scale_near_height n hlarge
    have hbase := (hgeo j).trans_eq (wired_horizontalRectangle_probability_eq_origin (criticalParameters q) μ hμ _ _ _)
    have hsub := (horizontalRectangle_mono_width (0,0) w (16*kstScale (1+j))
      (2*kstScale (1+j)) (by omega)).trans
        (horizontalRectangle_mono_height (0,0) w (2*kstScale (1+j)) n hheight)
    exact (min_le_left _ _).trans (hbase.trans (measureReal_mono hsub))
  · have hw' : w ≤ 3072 := by omega
    have hsub := (horizontalRectangle_mono_width (0,0) w 3072 0 hw').trans
      (horizontalRectangle_mono_height (0,0) w 0 n (Nat.zero_le n))
    exact (min_le_right _ _).trans (measureReal_mono hsub)

end
end PottsContinuity.BD12
