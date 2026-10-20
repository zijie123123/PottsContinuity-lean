module

public import PottsContinuity.BD12.DRTWiredIntegratedGrowth
public import PottsContinuity.BD12.DRTStretchedSummable
public import Mathlib.Tactic

/-! The first bootstrap stage for the actual wired sequence: a sublinear
power bound on its genuine partial sums yields a summable lower-parameter tail. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter Set
noncomputable section

/-- The finite endpoint bound yields stretched exponential decay from the
source partial-sum power bound. -/
theorem drt_wired_one_arm_stretched_bound (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) ≤ γ) (α : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hS : drtWiredOneArmSum q γ n ≤ (n : ℝ) ^ (1 - α)) :
    drtWiredOneArmMean q β n ≤
      Real.exp (-(drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β)) * (n : ℝ) ^ α) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hSpos : 0 < drtWiredOneArmSum q γ n :=
    lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q γ n hn)
  have hpow : (n : ℝ) ^ α * (n : ℝ) ^ (1 - α) = n := by
    rw [← Real.rpow_add hnpos]
    simp only [add_sub_cancel, Real.rpow_one]
  have hratio : (n : ℝ) ^ α ≤ (n : ℝ) / drtWiredOneArmSum q γ n := by
    apply (le_div_iff₀ hSpos).mpr
    exact (mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hnpos.le _)).trans_eq hpow
  have hc := drtWiredGrowthCoefficient_pos q γ
  have hg : 0 ≤ (γ : ℝ) - β := sub_nonneg.mpr hβγ
  apply (drt_wired_one_arm_endpoint_decay q hq β γ hβγ n hn).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hratio (mul_nonneg hc.le hg)
  calc
    -(drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n) * ((γ : ℝ) - β) =
        -(drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) * ((n : ℝ) / drtWiredOneArmSum q γ n)) := by ring
    _ ≤ -(drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) * (n : ℝ) ^ α) := neg_le_neg h
    _ = -(drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β)) * (n : ℝ) ^ α := by ring

/-- An eventual sublinear power bound at the upper parameter makes the actual
one-arm sequence summable at every smaller positive parameter. -/
theorem drt_wired_one_arm_summable_of_sublinear_sum (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) < γ) (α : ℝ) (hα : 0 < α)
    (hS : ∀ᶠ n : ℕ in atTop, drtWiredOneArmSum q γ n ≤ (n : ℝ) ^ (1 - α)) :
    Summable (drtWiredOneArmMean q β) := by
  have hδ : 0 < drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) :=
    mul_pos (drtWiredGrowthCoefficient_pos q γ) (sub_pos.mpr hβγ)
  apply (drt_summable_stretched_exponential _ α hδ hα).of_norm_bounded_eventually_nat
  filter_upwards [hS, eventually_ge_atTop 1] with n hSn hn
  rw [Real.norm_eq_abs, abs_of_nonneg (drtWiredOneArmMean_mem_Icc q β n).1]
  exact drt_wired_one_arm_stretched_bound q hq β γ hβγ.le α n hn hSn

end
end PottsContinuity.BD12
