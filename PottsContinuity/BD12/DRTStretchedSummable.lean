module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.PSeries

/-! Summability of stretched exponential tails, used in the first-to-second
stage of the DRT scalar bootstrap. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter

/-- Every positive-power stretched exponential has a finite series. -/
theorem drt_summable_stretched_exponential (δ α : ℝ) (hδ : 0 < δ) (hα : 0 < α) :
    Summable (fun n : ℕ => Real.exp (-δ * (n : ℝ) ^ α)) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have ho := (isLittleO_exp_neg_mul_rpow_atTop hδ (-2 / α)).comp_tendsto hlim
  have heq : (fun n : ℕ => ((n : ℝ) ^ α) ^ (-2 / α)) = fun n : ℕ => (n : ℝ) ^ (-2 : ℝ) := by
    funext n
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    field_simp
  change (fun n : ℕ => Real.exp (-δ * (n : ℝ) ^ α)) =o[atTop]
    (fun n : ℕ => ((n : ℝ) ^ α) ^ (-2 / α)) at ho
  rw [heq] at ho
  exact summable_of_isBigO_nat (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)) ho.isBigO

end PottsContinuity.BD12
