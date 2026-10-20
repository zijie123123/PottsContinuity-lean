module

public import PottsContinuity.BD12.DRTWiredStretchedDecay
public import Mathlib.Tactic

/-! The two-stage DRT bootstrap for the actual wired one-arm sequence.
A genuine sublinear partial-sum bound supplies both parameter decreases. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter Set
noncomputable section

/-- Summability at an upper parameter implies exponential decay below it. -/
theorem drt_wired_one_arm_exponential_of_summable (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) < γ) (hseries : Summable (drtWiredOneArmMean q γ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → drtWiredOneArmMean q β n ≤ Real.exp (-c * n) := by
  let S := ∑' k, drtWiredOneArmMean q γ k
  have hSbound (n : ℕ) : drtWiredOneArmSum q γ n ≤ S :=
    hseries.sum_le_tsum (Finset.range n) (fun k _ => (drtWiredOneArmMean_mem_Icc q γ k).1)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one
    ((drtWiredOneArmSum_ge_one q γ 1 le_rfl).trans (hSbound 1))
  let c := drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) / S
  have hc : 0 < c := div_pos (mul_pos (drtWiredGrowthCoefficient_pos q γ) (sub_pos.mpr hβγ)) hSpos
  refine ⟨c, hc, fun n hn => ?_⟩
  have hSn : 0 < drtWiredOneArmSum q γ n :=
    lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q γ n hn)
  have hcoef : drtWiredGrowthCoefficient q γ * (n : ℝ) / S ≤
      drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n :=
    div_le_div_of_nonneg_left
      (mul_nonneg (drtWiredGrowthCoefficient_pos q γ).le (Nat.cast_nonneg n)) hSn (hSbound n)
  apply (drt_wired_one_arm_endpoint_decay q hq β γ hβγ.le n hn).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hcoef (sub_pos.mpr hβγ).le
  calc
    -(drtWiredGrowthCoefficient q γ * (n : ℝ) / drtWiredOneArmSum q γ n) * ((γ : ℝ) - β) ≤
        -(drtWiredGrowthCoefficient q γ * (n : ℝ) / S * ((γ : ℝ) - β)) := by linarith only [h]
    _ = -c * n := by dsimp only [c]; ring

/-- Both stages together: a sublinear source sum at delta gives exponential
decay at beta, for every positive beta<gamma<delta. -/
theorem drt_wired_one_arm_exponential_of_sublinear_sum (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ δ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) < γ) (hγδ : (γ : ℝ) < δ)
    (α : ℝ) (hα : 0 < α)
    (hS : ∀ᶠ n : ℕ in atTop, drtWiredOneArmSum q δ n ≤ (n : ℝ) ^ (1 - α)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → drtWiredOneArmMean q β n ≤ Real.exp (-c * n) :=
  drt_wired_one_arm_exponential_of_summable q hq β γ hβγ
    (drt_wired_one_arm_summable_of_sublinear_sum q hq γ δ hγδ α hα hS)

end
end PottsContinuity.BD12
