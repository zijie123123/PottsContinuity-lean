module

public import PottsContinuity.Thm3.RSW.AnnulusArmBound

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The actual uniform-annulus alternative gives a polynomial lower bound
on the SAME free infinite-volume arm at every positive integer scale. -/
theorem oneArm_polynomial_lower_of_uniform_annulus
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (a : ℝ) (_ha : 0 < a)
    (hannulus : ∀ n : ℕ, 1 ≤ n → a ≤ RSW.annulusProbability (RSW.selfDualParameters q) 8 n) :
    ∀ n : ℕ, 1 ≤ n → a/25 ≤ (n : ℝ)^2*RSW.oneArmProbability μ n := by
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 4*(n : ℝ)+1 ≤ 5*(n : ℝ) := by linarith only [hnR]
  have hp := pow_le_pow_left₀ (show 0 ≤ 4*(n : ℝ)+1 by positivity) hbase 2
  have hcoeff : (4*(n : ℝ)+1)^2 ≤ 25*(n : ℝ)^2 := by nlinarith only [hp]
  have hb := (hannulus n hn).trans ((RSW.annulusProbability_le_polynomial_mul_oneArm
    (RSW.selfDualParameters q) μ hμ 8 n).trans
      (mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ RSW.oneArmProbability μ n from ENNReal.toReal_nonneg)))
  linarith only [hb]

end
end PottsContinuity.Thm3.Prop4
