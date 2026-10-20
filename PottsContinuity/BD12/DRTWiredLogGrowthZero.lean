module

public import PottsContinuity.BD12.DRTWiredLogAverageIntegrated
public import Mathlib.Tactic

/-! A zero actual one-arm limit forces logarithmically sublinear partial sums
at every smaller positive parameter. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter Set
open scoped Topology
noncomputable section

/-- The integrated averaged inequality forces log S_n/log n to zero below
any parameter where the actual finite wired one-arm sequence tends to zero. -/
theorem drt_wired_log_sum_tendsto_zero_of_oneArmZero (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) < γ)
    (hzero : Tendsto (drtWiredOneArmMean q γ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (drtWiredOneArmSum q β n) / Real.log n) atTop (𝓝 0) := by
  have havg : Tendsto (fun n => drtWiredLogAverage q n γ) atTop (𝓝 0) :=
    drt_log_average_tendsto (drtWiredOneArmMean q γ) 0 hzero
  let K := drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β)
  have hK : 0 < K := mul_pos (drtWiredGrowthCoefficient_pos q γ) (sub_pos.mpr hβγ)
  have hlim := havg.div_const K
  simp only [zero_div] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (Real.log_nonneg (drtWiredOneArmSum_ge_one q β n (by omega)))
      (Real.log_pos (by exact_mod_cast hn)).le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hT : 0 ≤ drtWiredLogAverage q n β := by
      change 0 ≤ (∑ i ∈ Finset.range n, drtWiredOneArmMean q β (i+1) / (i+1 : ℕ)) / Real.log n
      exact div_nonneg (Finset.sum_nonneg (fun i _ =>
        div_nonneg (drtWiredOneArmMean_mem_Icc q β (i+1)).1 (Nat.cast_nonneg _))) hlog.le
    have hi := drt_wired_log_average_integrated_lower_bound q hq β γ hβγ.le n hn
    have hupper : Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n ≤ drtWiredLogAverage q n γ / K := by
      apply (le_div_iff₀ hK).mpr
      calc
        Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n * K =
            drtWiredGrowthCoefficient q γ * ((γ : ℝ) - β) * Real.log (drtWiredOneArmSum q β (n+1)) / Real.log n := by
          dsimp only [K]
          ring
        _ ≤ drtWiredLogAverage q n γ := by linarith only [hi, hT]
    have hS : drtWiredOneArmSum q β n ≤ drtWiredOneArmSum q β (n+1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun i _ _ => (drtWiredOneArmMean_mem_Icc q β i).1)
    have hSpos : 0 < drtWiredOneArmSum q β n :=
      lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q β n (by omega))
    exact (div_le_div_of_nonneg_right (Real.log_le_log hSpos hS) hlog.le).trans hupper

/-- A concrete sublinear power bound, ready for the two-stage bootstrap. -/
theorem drt_wired_sublinear_sum_of_oneArmZero (q : Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β γ : Ioi (0 : ℝ)) (hβγ : (β : ℝ) < γ)
    (hzero : Tendsto (drtWiredOneArmMean q γ) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, drtWiredOneArmSum q β n ≤ (n : ℝ) ^ (1 - (1/2 : ℝ)) := by
  have hsmall := (drt_wired_log_sum_tendsto_zero_of_oneArmZero q hq β γ hβγ hzero).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hs hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hSpos : 0 < drtWiredOneArmSum q β n :=
    lt_of_lt_of_le zero_lt_one (drtWiredOneArmSum_ge_one q β n (by omega))
  rw [Real.rpow_def_of_pos hnpos]
  apply (Real.log_le_iff_le_exp hSpos).mp
  have h := (div_lt_iff₀ hlog).mp hs
  linarith only [h]

end
end PottsContinuity.BD12
