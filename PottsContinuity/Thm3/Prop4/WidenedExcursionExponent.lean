module

public import PottsContinuity.Thm3.Prop4.UniformExcursionConvolution
public import PottsContinuity.Thm3.Prop4.RadiusTube
public import PottsContinuity.Thm3.Prop4.PowerCutoff

/-!
# The widened proof tube is an exact instance of the original tube definition

At every scale at least two, any positive radius is a real power of that
scale. The uniform maximal-record estimate allows this auxiliary exponent
to depend on the scale, while its coefficient stays independent of it.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- Every positive radius is exactly a real power of a fixed scale above one. -/
theorem exists_scale_exponent_for_positive_radius {n : ℕ} (hn : 2 ≤ n)
    (R : ℝ) (hR : 0 < R) : ∃ η : ℝ, (n : ℝ)^η = R := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
  refine ⟨Real.log R/Real.log (n : ℝ),?_⟩
  rw [Real.rpow_def_of_pos hn0]
  have heq : Real.log (n : ℝ)*(Real.log R/Real.log (n : ℝ)) = Real.log R := by
    field_simp
  rw [heq,Real.exp_log hR]

/-- The original Euclidean tube definition realizes the widened proof tube
exactly, with no change to its cutoff or to the maximal-vertex definition. -/
theorem exists_widened_excursion_exponent {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) :
    ∃ η : ℝ, (n : ℝ)^η = 4*(n : ℝ)^ε ∧
      ∀ u v : ℤ × ℤ, inductionTube n η u v = widenedInductionTube n ε u v := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨η,hη⟩ := exists_scale_exponent_for_positive_radius hn (4*(n : ℝ)^ε) (by positivity)
  refine ⟨η,hη,?_⟩
  intro u v
  rw [inductionTube_eq_radiusTube,hη]
  rfl

/-- The exact square-arm cutoff is admissible beyond a common scale for each
sublinear nonnegative exponent; every omitted small scale remains explicit. -/
theorem eventually_split_power_cutoff_admissible (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ (n : ℝ)^ε ∧ 2*⌈(n : ℝ)^ε⌉₊ ≤ 2*n-2 := by
  have hpow := eventually_rpow_le_half_mul (α := 1) (β := ε) (c₀ := 1) hε1 zero_lt_one
  filter_upwards [hpow,eventually_ge_atTop 2] with n hn hn2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hceil : ⌈(n : ℝ)^ε⌉₊ ≤ n-1 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
    simp only [Real.rpow_one] at hn
    exact hn.trans (by linarith only [hnR])
  exact ⟨hn2,Real.one_le_rpow (by linarith only [hnR]) hε,by omega⟩

end PottsContinuity.Thm3.Prop4
