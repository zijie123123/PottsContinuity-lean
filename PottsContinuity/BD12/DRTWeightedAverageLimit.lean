module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Weighted averages of convergent real sequences and the logarithmic
normalization used in DRT's mean-field argument. -/

@[expose] public section

namespace PottsContinuity.BD12
open Filter Asymptotics
open scoped Topology

/-- Divergent sums of nonnegative weights preserve the limit of a sequence. -/
theorem drt_weighted_average_tendsto (u w : ℕ → ℝ) (l : ℝ)
    (hu : Tendsto u atTop (𝓝 l)) (hw : ∀ n, 0 ≤ w n)
    (hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, w i * u i) /
      (∑ i ∈ Finset.range n, w i)) atTop (𝓝 l) := by
  have ho : (fun n => w n * (u n - l)) =o[atTop] w := by
    have h := (isBigO_refl w atTop).mul_isLittleO ((isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hu))
    simpa only [mul_one] using h
  have hs := (ho.sum_range hw hW).tendsto_div_nhds_zero
  have hlim := hs.add_const l
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hW.eventually (eventually_gt_atTop 0)] with n hn
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  field_simp
  ring

/-- Harmonic normalization is asymptotically logarithmic. -/
theorem drt_harmonic_div_log_tendsto :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_harmonic_sub_log.div_atTop hlog).add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
  field_simp
  ring

end PottsContinuity.BD12
