module

public import PottsContinuity.BD12.KSTCoverTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Endpoint, order and continuity facts for KST's explicit cover transform.
These are scalar inputs to the remaining scale induction. -/

@[expose] public section

namespace PottsContinuity.BD12

@[simp] theorem kstCoverTransform_zero : kstCoverTransform 0 = 0 := by
  norm_num [kstCoverTransform]

@[simp] theorem kstCoverTransform_one : kstCoverTransform 1 = 1 := by
  norm_num [kstCoverTransform]

theorem kstCoverTransform_strictMonoOn : StrictMonoOn kstCoverTransform (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hr : (1 - y) ^ ((2000 : ℝ)⁻¹) < (1 - x) ^ ((2000 : ℝ)⁻¹) :=
    Real.rpow_lt_rpow (sub_nonneg.mpr hy.2) (by linarith only [hxy]) (by positivity)
  have hr1 : (1 - x) ^ ((2000 : ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one (sub_nonneg.mpr hx.2) (by linarith only [hx.1]) (by positivity)
  exact pow_lt_pow_left₀ (by linarith only [hr]) (sub_nonneg.mpr hr1) (by decide)

theorem kstCoverTransform_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < kstCoverTransform x := by
  have h := kstCoverTransform_strictMonoOn ⟨le_rfl, zero_le_one⟩ ⟨hx.le, hx1⟩ hx
  simpa only [kstCoverTransform_zero] using h

end PottsContinuity.BD12
