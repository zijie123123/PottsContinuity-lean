module

public import PottsContinuity.BD12.DRTWeightedAverageLimit

/-! Convergence of DRT's logarithmically normalized averages.
The sequence is arbitrary and the actual harmonic sums supply normalization. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter
open scoped Topology
noncomputable section

/-- The source T_n, with the displayed logarithmic normalization. -/
def drtLogAverage (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, u (i+1) / (i+1 : ℕ)) / Real.log n

/-- DRT's logarithmically weighted averages converge to the sequence limit. -/
theorem drt_log_average_tendsto (u : ℕ → ℝ) (l : ℝ)
    (hu : Tendsto u atTop (𝓝 l)) : Tendsto (drtLogAverage u) atTop (𝓝 l) := by
  let w : ℕ → ℝ := fun i => ((i+1 : ℕ) : ℝ)⁻¹
  have hw (n : ℕ) : (∑ i ∈ Finset.range n, w i) = (harmonic n : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, w]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hH : Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
    have h := Real.tendsto_harmonic_sub_log.add_atTop hlog
    convert h using 1
    funext n
    ring
  have hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop := by
    simpa only [hw] using hH
  have havg := drt_weighted_average_tendsto (fun i => u (i+1)) w l
    (hu.comp (tendsto_add_atTop_nat 1)) (fun i => inv_nonneg.mpr (Nat.cast_nonneg _)) hW
  have h := havg.mul drt_harmonic_div_log_tendsto
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [hH.eventually (eventually_gt_atTop 0), hlog.eventually (eventually_gt_atTop 0)] with n hn hln
  simp only [hw]
  unfold drtLogAverage
  simp only [w, div_eq_mul_inv, mul_comm (u _)]
  field_simp

end
end PottsContinuity.BD12
