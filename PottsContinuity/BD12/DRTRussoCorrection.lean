module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

/-!
# The coefficient of the DRT Russo formula

The derivative formula displayed in the proof of Theorem 1.2 of arXiv:1705.03104v2 has the
coefficient `J/(exp(βJ) - 1)`, which is smaller than the correct `J exp(βJ)/(exp(βJ) - 1)`; the
correct formula is `drt_russo_corrected` in `PottsContinuity.BD12.DRTRusso`. This module proves the
elementary inequality between the two coefficients, so the printed lower bound remains valid for
nonnegative covariances.
-/

@[expose] public section

namespace PottsContinuity.BD12

/-- With nonnegative covariance the corrected coefficient still implies the
smaller lower-bound coefficient used in the source's sharpness argument. -/
theorem drt_russo_coefficient_lower_bound (β J C : ℝ)
    (hβ : 0 < β) (hJ : 0 < J) (hC : 0 ≤ C) :
    J / (Real.exp (β * J) - 1) * C ≤
      (J * Real.exp (β * J)) / (Real.exp (β * J) - 1) * C := by
  have he : 1 < Real.exp (β * J) := Real.one_lt_exp_iff.mpr (mul_pos hβ hJ)
  apply mul_le_mul_of_nonneg_right _ hC
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr he).le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he.le hJ.le

end PottsContinuity.BD12
