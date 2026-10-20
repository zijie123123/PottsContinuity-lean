module

public import PottsContinuity.BD12.DRTWiredLogGrowthZero
public import PottsContinuity.BD12.DRTWiredExponentialBootstrap
public import Mathlib.Tactic

/-! Sharpness of the finite wired sequence below an upper parameter with zero
one-arm limit. Below a critical point that limit follows from wired non-percolation
(`drtWiredOneArmMean_tendsto_zero_of_wired_nonpercolation` in `BD12.DRTWiredZeroLimit`);
the two are combined in `drt_genuine_subcritical_exponential_decay`
(`BD12.DRTGenuineSubcriticalSharpness`). -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter Set
open scoped Topology

/-- Exponential decay at every positive lower parameter follows from a zero
actual finite one-arm limit at the upper parameter. -/
theorem drt_wired_exponential_decay_of_oneArmZero (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β δ : Ioi (0 : ℝ)) (hβδ : (β : ℝ) < δ)
    (hzero : Tendsto (drtWiredOneArmMean q δ) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → drtWiredOneArmMean q β n ≤ Real.exp (-c * n) := by
  obtain ⟨y, hβy, hyδ⟩ := exists_between hβδ
  obtain ⟨x, hβx, hxy⟩ := exists_between hβy
  let γ : Ioi (0 : ℝ) := ⟨y, β.property.trans hβy⟩
  let η : Ioi (0 : ℝ) := ⟨x, β.property.trans hβx⟩
  exact drt_wired_one_arm_exponential_of_sublinear_sum q hq β η γ hβx hxy (1/2) (by norm_num)
    (drt_wired_sublinear_sum_of_oneArmZero q hq γ δ hyδ hzero)

end PottsContinuity.BD12
