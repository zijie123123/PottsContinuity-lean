module

public import PottsContinuity.BD12.DRTWiredOneArmExpression
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Integrated differential inequality for the actual finite wired sequence.
The endpoint denominator is its genuine source partial sum. -/

@[expose] public section

namespace PottsContinuity.BD12
open Set
noncomputable section

/-- The source integrating-factor estimate, with all finite-model inputs proved. -/
theorem drt_wired_one_arm_integrated_growth (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) (n : ℕ) (hn : 1 ≤ n) :
    drtWiredOneArmMean q β n ≤ drtWiredOneArmMean q γ n *
      Real.exp (-(drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n) * ((γ : ℝ) - β)) := by
  let F := drtWiredOneArmExpression q n
  let c := drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n
  have hdiff (x : ℝ) (hx : x ∈ Icc (β : ℝ) γ) : DifferentiableAt ℝ F x :=
    drtWiredOneArmExpression_differentiableAt q n x (β.property.trans_le hx.1)
  have hcont : ContinuousOn F (Icc (β : ℝ) γ) := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  have hgrowth (x : ℝ) (hx : x ∈ Ioo (β : ℝ) γ) : c * F x ≤ deriv F x := by
    let b : Ioi (0 : ℝ) := ⟨x, β.property.trans hx.1⟩
    have hbγ : (b : ℝ) ≤ γ := hx.2.le
    have hS : drtWiredOneArmSum q b n ≤ drtWiredOneArmSum q γ n :=
      Finset.sum_le_sum (fun k _ => drtWiredOneArmMean_mono_beta q hq b γ hbγ k)
    have hSpos : 0 < drtWiredOneArmSum q b n :=
      lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q b n hn)
    have hcoef : c ≤ drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q b n :=
      div_le_div_of_nonneg_left
        (mul_nonneg (drtWiredGrowthCoefficient_pos q γ).le (Nat.cast_nonneg n)) hSpos hS
    exact (mul_le_mul_of_nonneg_right hcoef (drtWiredOneArmMean_mem_Icc q b n).1).trans
      (drt_wired_one_arm_source_growth q hq b γ hbγ n hn)
  exact drt_exponential_bound_of_derivative_growth F (deriv F) β γ c hβγ hcont
    (fun x hx => (hdiff x ⟨hx.1.le,hx.2.le⟩).hasDerivAt) hgrowth

/-- A probability bound at the right endpoint removes the prefactor. -/
theorem drt_wired_one_arm_endpoint_decay (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) (n : ℕ) (hn : 1 ≤ n) :
    drtWiredOneArmMean q β n ≤
      Real.exp (-(drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n) * ((γ : ℝ) - β)) :=
  (drt_wired_one_arm_integrated_growth q hq β γ hβγ n hn).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (drtWiredOneArmMean_mem_Icc q γ n).2
      (Real.exp_pos _).le)

end
end PottsContinuity.BD12
