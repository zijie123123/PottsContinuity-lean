module

public import PottsContinuity.BD12.DRTLogAverageLimit
public import PottsContinuity.BD12.DRTWiredOneArmExpression
public import PottsContinuity.BD12.DRTLogPartialSum
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! The averaged derivative estimate for the actual wired sequence in DRT.
The finite logarithmic telescoping estimate is applied to its actual sums. -/

@[expose] public section

namespace PottsContinuity.BD12
open Set
noncomputable section

/-- The actual wired analogue of the source logarithmic average T_n. -/
def drtWiredLogAverage (q : Ioi (0 : ℝ)) (n : ℕ) (t : ℝ) : ℝ :=
  drtLogAverage (fun k => drtWiredOneArmExpression q k t) n

/-- Differentiate the actual finite average at a positive parameter. -/
theorem drtWiredLogAverage_hasDerivAt (q : Ioi (0 : ℝ)) (n : ℕ) (β : Ioi (0 : ℝ)) :
    HasDerivAt (drtWiredLogAverage q n)
      ((∑ i ∈ Finset.range n, deriv (drtWiredOneArmExpression q (i+1)) β / (i+1 : ℕ)) / Real.log n) β := by
  exact (HasDerivAt.fun_sum (fun i _ =>
    (drtWiredOneArmExpression_differentiableAt q (i+1) β β.property).hasDerivAt.div_const
      ((i+1 : ℕ) : ℝ))).div_const (Real.log n)

/-- Source averaged growth bound for every q>=1 and 0<beta<=beta_0. -/
theorem drt_wired_log_average_derivative_lower_bound (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β β₀ : Ioi (0 : ℝ)) (hβ : (β : ℝ) ≤ β₀) (n : ℕ) (hn : 2 ≤ n) :
    drtWiredGrowthCoefficient q β₀ * Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n ≤
      deriv (drtWiredLogAverage q n) β := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  let F := drtWiredOneArmExpression q
  let c := drtWiredGrowthCoefficient q β₀
  have hzero : 0 < F 0 β := by
    change 0 < drtWiredOneArmMean q β 0
    rw [drtWiredOneArmMean_zero]
    exact zero_lt_one
  have hS1 : drtPartialSum F 1 β = 1 := by
    simp only [drtPartialSum, Finset.sum_range_one]
    exact (show F 0 β = drtWiredOneArmMean q β 0 from rfl).trans (drtWiredOneArmMean_zero q β)
  have htel := drt_log_partial_sum_le_sum_ratio F β
    (fun k => (drtWiredOneArmMean_mem_Icc q β k).1) hzero n
  rw [hS1, Real.log_one, sub_zero] at htel
  have hsum : c * (∑ i ∈ Finset.range n, F (i+1) β / drtPartialSum F (i+1) β) ≤
      ∑ i ∈ Finset.range n, deriv (F (i+1)) β / (i+1 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : (0 : ℝ) < (i+1 : ℕ) := by positivity
    have hS : 0 < drtPartialSum F (i+1) β :=
      drtPartialSum_pos F β (fun k => (drtWiredOneArmMean_mem_Icc q β k).1) hzero (i+1) (by omega)
    have hg := drt_wired_one_arm_source_growth q hq β β₀ hβ (i+1) (by omega)
    calc
      c * (F (i+1) β / drtPartialSum F (i+1) β) =
          ((c * ((i+1 : ℕ) : ℝ) / drtPartialSum F (i+1) β) * F (i+1) β) / (i+1 : ℕ) := by
        field_simp
      _ ≤ deriv (F (i+1)) β / (i+1 : ℕ) := div_le_div_of_nonneg_right hg hi.le
  rw [(drtWiredLogAverage_hasDerivAt q n β).deriv]
  exact div_le_div_of_nonneg_right
    ((mul_le_mul_of_nonneg_left htel (drtWiredGrowthCoefficient_pos q β₀).le).trans hsum) hlog.le

end
end PottsContinuity.BD12
