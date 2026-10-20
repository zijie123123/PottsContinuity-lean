module

public import PottsContinuity.BD12.DRTWiredLogAverageDerivative
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Integration of the actual averaged growth bound on a positive interval. -/

@[expose] public section

namespace PottsContinuity.BD12
open Set
noncomputable section

/-- DRT's finite integrated logarithmic estimate, without analytic premises. -/
theorem drt_wired_log_average_integrated_lower_bound (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) (n : ℕ) (hn : 2 ≤ n) :
    drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) * Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n ≤
      drtWiredLogAverage q n γ - drtWiredLogAverage q n β := by
  let T := drtWiredLogAverage q n
  let C := drtWiredGrowthCoefficient q γ * Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n
  have hD (x : ℝ) (hx : x ∈ Icc (β : ℝ) γ) : DifferentiableAt ℝ T x :=
    (drtWiredLogAverage_hasDerivAt q n ⟨x,β.property.trans_le hx.1⟩).differentiableAt
  have hcont : ContinuousOn T (Icc (β : ℝ) γ) := fun x hx => (hD x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ T (interior (Icc (β : ℝ) γ)) := by
    rw [interior_Icc]
    exact fun x hx => (hD x ⟨hx.1.le,hx.2.le⟩).differentiableWithinAt
  have hbound : ∀ x ∈ interior (Icc (β : ℝ) γ), C ≤ deriv T x := by
    rw [interior_Icc]
    intro x hx
    let b : Ioi (0 : ℝ) := ⟨x,β.property.trans hx.1⟩
    have hS : drtWiredOneArmSum q β (n+1) ≤ drtWiredOneArmSum q b (n+1) :=
      Finset.sum_le_sum (fun k _ => drtWiredOneArmMean_mono_beta q hq β b hx.1.le k)
    have hSpos : 0 < drtWiredOneArmSum q β (n+1) :=
      lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q β (n+1) (by omega))
    have hln : 0 ≤ Real.log (n : ℝ) := (Real.log_pos (by exact_mod_cast hn)).le
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.log_le_log hSpos hS) (drtWiredGrowthCoefficient_pos q γ).le) hln).trans
        (drt_wired_log_average_derivative_lower_bound q hq b γ hx.2.le n hn)
  have h := (convex_Icc (β : ℝ) (γ : ℝ)).mul_sub_le_image_sub_of_le_deriv hcont hdiff hbound
    β ⟨le_rfl,hβγ⟩ γ ⟨hβγ,le_rfl⟩ hβγ
  convert h using 1; dsimp only [C, T]; ring

end
end PottsContinuity.BD12
