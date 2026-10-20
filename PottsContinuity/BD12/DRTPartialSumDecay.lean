module

public import PottsContinuity.BD12.DRTExponentialGrowth

/-! The partial sums Sigma_n(beta) in DRT's technical scalar lemma. The bounded
partial-sum exponential step and the two-stage bootstrap for the wired one-arm
sequence are proved in `BD12.DRTWiredExponentialBootstrap`
(`drt_wired_one_arm_exponential_of_sublinear_sum`). -/

@[expose] public section

namespace PottsContinuity.BD12
open Set

/-- DRT's Sigma_n(beta), including the actual empty sum at n=0. -/
def drtPartialSum (F : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, F k x

end PottsContinuity.BD12
