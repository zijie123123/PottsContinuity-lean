module

public import PottsContinuity.Thm3.Prop4.TubeExitRegions

/-!
# Uniform strict-core crossings from a smaller fractional exponent

The existing bulk theorem is applied at epsilon/2. Eventually its entire
radius-four tube lies strictly between the signed heights of the source
exit arcs for the outer radius-four tube at exponent epsilon.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- A common geometric cutoff separates the inner and outer signed heights. -/
theorem exists_tube_strict_interior_scale (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      8*(n : ℝ)^(ε/2) ≤ 4*(n : ℝ)^ε-1 := by
  have h := ((tendsto_rpow_atTop (by linarith : 0 < ε/2)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ))
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hp := hN n ((le_max_left _ _).trans hn)
  change 4 ≤ (n : ℝ)^(ε/2) at hp
  have heq : ((n : ℝ)^(ε/2))^2 = (n : ℝ)^ε := by
    rw [← Real.rpow_two,← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [← heq]
  nlinarith only [hp,mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (Nat.cast_nonneg n) (ε/2))]

end
end PottsContinuity.Thm3.Prop4
