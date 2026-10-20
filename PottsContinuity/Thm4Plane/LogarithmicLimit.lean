module

public import Mathlib
public import PottsContinuity.Frozen.Defs

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open scoped ENNReal

/-- A polynomial lower bound on the free box-boundary connection probability
forces its logarithmic rate to vanish. The premise is exactly the plane-bound
output used by the final step of the source proof; this lemma does not prove
that bound. -/
theorem boxBoundary_logarithmic_rate_zero_of_polynomial_lower_bound
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ)
    (c : ℝ) (hc : 0 < c)
    (hpoly : ∀ n : ℕ, 1 ≤ n →
      c / (n : ℝ) ^ 16 ≤ μ.real {ω | ∃ y ∈ vertexBoundary (box n),
        (rcInfiniteOpenGraph ω).Reachable (0, 0) y}) :
    Tendsto
      (fun n : ℕ => 1 / (n : ℝ) * Real.log (μ.real
        {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
      atTop (𝓝 0) := by
  let event (n : ℕ) : Set (squareLattice.edgeSet → Bool) :=
    {ω | ∃ y ∈ vertexBoundary (box n),
      (rcInfiniteOpenGraph ω).Reachable (0, 0) y}
  have hlogNat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    convert h using 1
    ext n
    simp
  have hconstant : Tendsto
      (fun n : ℕ => Real.log c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log c)
  have hsmall : Tendsto
      (fun n : ℕ => Real.log c / (n : ℝ) -
        16 * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    convert hconstant.add (hlogNat.const_mul (-16)) using 1 <;>
      ext n <;> ring_nf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hsmall tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
    have hdenom : 0 < (n : ℝ) ^ 16 := pow_pos hnpos _
    have hbase : 0 < c / (n : ℝ) ^ 16 := div_pos hc hdenom
    have hprobpos : 0 < μ.real (event n) := lt_of_lt_of_le hbase (hpoly n hn)
    have hloglower : Real.log (c / (n : ℝ) ^ 16) ≤ Real.log (μ.real (event n)) :=
      Real.log_le_log hbase (hpoly n hn)
    have hlogdiv : Real.log (c / (n : ℝ) ^ 16) =
        Real.log c - 16 * Real.log (n : ℝ) := by
      rw [Real.log_div hc.ne' (pow_ne_zero 16 hnne), Real.log_pow]
      norm_num
    have hscaled :
        1 / (n : ℝ) * (Real.log c - 16 * Real.log (n : ℝ)) ≤
          1 / (n : ℝ) * Real.log (μ.real (event n)) := by
      calc
        _ = 1 / (n : ℝ) * Real.log (c / (n : ℝ) ^ 16) := by rw [hlogdiv]
        _ ≤ _ := mul_le_mul_of_nonneg_left hloglower (le_of_lt (one_div_pos.mpr hnpos))
    have hsmall_eq :
        Real.log c / (n : ℝ) - 16 * (Real.log (n : ℝ) / (n : ℝ)) =
          1 / (n : ℝ) * (Real.log c - 16 * Real.log (n : ℝ)) := by
      field_simp [hnne]
    rw [hsmall_eq]
    exact hscaled
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hprobpos : 0 < μ.real (event n) :=
      lt_of_lt_of_le (div_pos hc (pow_pos hnpos _)) (hpoly n hn)
    have hmass : μ (event n) ≤ 1 := by
      calc
        μ (event n) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := hμ.1.measure_univ
    have hprob : μ.real (event n) ≤ 1 := by
      simpa [Measure.real_def] using ENNReal.toReal_mono ENNReal.one_ne_top hmass
    have hlogupper : Real.log (μ.real (event n)) ≤ 0 := by
      calc
        Real.log (μ.real (event n)) ≤ Real.log 1 :=
          Real.log_le_log hprobpos hprob
        _ = 0 := Real.log_one
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (one_div_pos.mpr hnpos)) hlogupper

end PottsContinuity.Thm4Plane
