module

public import PottsContinuity.Thm4Plane.LogarithmicLimit

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open scoped ENNReal

/-- The source screen is run at scale `16 * m` and gives a lower bound with
that source scale in the denominator. This rescales the coefficient to the
box-boundary form consumed by the logarithmic squeeze. -/
theorem boxBoundary_logarithmic_rate_zero_of_sixteen_scale_polynomial_lower_bound
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ)
    (c : ℝ) (hc : 0 < c)
    (hpoly : ∀ m : ℕ, 1 ≤ m →
      c / ((16 * m : ℕ) : ℝ) ^ 16 ≤ μ.real {ω | ∃ y ∈ vertexBoundary (box m),
        (rcInfiniteOpenGraph ω).Reachable (0, 0) y}) :
    Tendsto
      (fun n : ℕ => 1 / (n : ℝ) * Real.log (μ.real
        {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
      atTop (𝓝 0) := by
  have hc' : 0 < c / (16 : ℝ) ^ 16 := div_pos hc (by positivity)
  apply boxBoundary_logarithmic_rate_zero_of_polynomial_lower_bound
    p q μ hμ (c / (16 : ℝ) ^ 16) hc'
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hscale : ((16 * n : ℕ) : ℝ) = 16 * (n : ℝ) := by norm_cast
  have hscale_pow : ((16 * n : ℕ) : ℝ) ^ 16 =
      (16 : ℝ) ^ 16 * (n : ℝ) ^ 16 := by
    rw [hscale, mul_pow]
  have hconstant :
      (c / (16 : ℝ) ^ 16) / (n : ℝ) ^ 16 =
        c / ((16 * n : ℕ) : ℝ) ^ 16 := by
    rw [hscale_pow]
    field_simp [hnne]
  rw [hconstant]
  exact hpoly n hn

end PottsContinuity.Thm4Plane
