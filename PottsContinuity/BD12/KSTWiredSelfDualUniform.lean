module

public import PottsContinuity.BD12.KSTWiredConstructionInputs
public import PottsContinuity.BD12.KSTBridgePositive
public import PottsContinuity.BD12.KSTBridgeCoverExport

/-! Actual wired uniform bridge and aspect-eight crossing bounds at the
explicit self-dual parameter. No arm, construction or cascade premise remains. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- Uniform positive bridge probabilities on the integral geometric sequence. -/
theorem wired_selfDual_kst_bridges_uniform_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ μ.real (kstBridge (kstScale (1+j))) := by
  apply wired_kst_uniform_bridge_of_construction_bound (criticalParameters q) μ hμ 1
    kstWiredInputLower kstWiredInputLower_pos kstWiredInputLower_le_one
    (infinite_kstBridge_probability_pos _ 1 μ hμ (kstScale 1))
  exact wired_selfDual_kst_construction_inputs_lower q μ hμ

/-- Uniform actual horizontal crossing bounds at aspect eight and scales 768*4^j. -/
theorem wired_selfDual_aspect_eight_geometric_lower_bound (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (criticalParameters q).toP (criticalParameters q).toQ 1 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ j,
      c ≤ μ.real (horizontalRectangle (-8*(kstScale (1+j) : ℤ),-(kstScale (1+j) : ℤ))
        (16*kstScale (1+j)) (2*kstScale (1+j))) := by
  let : IsProbabilityMeasure μ := hμ.1
  obtain ⟨c,hc,hbound⟩ := wired_selfDual_kst_bridges_uniform_lower_bound q μ hμ
  have hc1 : c ≤ 1 := (hbound 0).trans measureReal_le_one
  refine ⟨kstCoverTransform c,kstCoverTransform_pos hc hc1,fun j => ?_⟩
  have hm : 192 ∣ kstScale (1+j) := ⟨4^(1+j),rfl⟩
  have hcover := wired_kst_bridge_cover_lower_bound (criticalParameters q) μ hμ
    (kstScale (1+j)) hm (kstScale_pos (1+j))
  have hmono := kstCoverTransform_strictMonoOn.monotoneOn ⟨hc.le,hc1⟩
    ⟨measureReal_nonneg,measureReal_le_one⟩ (hbound j)
  exact hmono.trans hcover

end
end PottsContinuity.BD12
