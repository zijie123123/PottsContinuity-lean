module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! The explicit finite-cover transform in KST's first relation. Its formula
and the polynomial square-root-trick implication include both endpoints. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section

/-- The source f_1, with the literal exponent 2000. -/
def kstCoverTransform (x : ℝ) : ℝ :=
  (1 - (1 - x) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℕ)

/-- Convert the polynomial cover/gluing bounds into the literal source transform. -/
theorem kstCoverTransform_le_of_polynomial (b x c : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hcover : (1 - x) ^ (2000 : ℕ) ≤ 1 - b) (hglue : x ^ (2000 : ℕ) ≤ c) :
    kstCoverTransform b ≤ c := by
  have hr : 1 - x ≤ (1 - b) ^ ((2000 : ℝ)⁻¹) :=
    (Real.le_rpow_inv_iff_of_pos (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hb.2)
      (by norm_num : (0 : ℝ) < 2000)).mpr (by
        rw [← Real.rpow_natCast] at hcover
        exact hcover)
  have hr1 : (1 - b) ^ ((2000 : ℝ)⁻¹) ≤ 1 :=
    Real.rpow_le_one (sub_nonneg.mpr hb.2) (by linarith only [hb.1]) (by positivity)
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hr1) (by linarith only [hr]) 2000).trans hglue

end
end PottsContinuity.BD12
