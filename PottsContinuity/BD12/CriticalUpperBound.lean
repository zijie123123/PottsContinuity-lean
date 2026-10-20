module

public import PottsContinuity.BD12.DRTGenuineSubcriticalSharpness
public import PottsContinuity.BD12.SelfDualSourceArmBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The genuine threshold is at most the explicit self-dual point, for every
real q>=1. Subcritical exponential decay contradicts the wired square bound. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK Filter
open scoped Topology

/-- The genuine critical parameter is no larger than the self-dual formula. -/
theorem genuine_criticalPoint_le_selfDual (q : Set.Ici (1 : ℝ)) (pc : ℝ)
    (hpc : IsRCCriticalPoint q pc) : pc ≤ (PD.rcCriticalParameter q : ℝ) := by
  by_contra h
  let θ := criticalParameters q
  let β := drtInverseTemperature θ
  have hp : edgeParameter θ < pc := lt_of_not_ge h
  have hβ : 1 - Real.exp (-(β : ℝ)) < pc := (drtInverseTemperature_physical θ).trans_lt hp
  obtain ⟨c,hc,hdecay⟩ := drt_genuine_subcritical_exponential_decay q pc hpc β hβ
  have hlim : Tendsto (fun n : ℕ => 2 * ((n : ℝ) * Real.exp (-c * n))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using ht.const_mul 2
  obtain ⟨n,hn,hs⟩ := ((eventually_ge_atTop 1).and
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))).exists
  have hb := selfDual_source_one_arm_polynomial_lower_bound q n
  have hprod : (n+1 : ℕ) * drtWiredOneArmMean
      ⟨(q : ℝ), (show (0 : ℝ) < (q : ℝ) from lt_of_lt_of_le one_pos q.property)⟩ β n ≤
      2 * ((n : ℝ) * Real.exp (-c * n)) := by
    calc
      _ ≤ (n+1 : ℕ) * Real.exp (-c * n) :=
        mul_le_mul_of_nonneg_left (hdecay n hn) (Nat.cast_nonneg (n+1))
      _ ≤ (2 * (n : ℝ)) * Real.exp (-c * n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show n+1 ≤ 2*n by omega)) (Real.exp_pos _).le
      _ = _ := by ring
  exact (not_lt_of_ge (hb.trans hprod)) hs

end PottsContinuity.BD12
