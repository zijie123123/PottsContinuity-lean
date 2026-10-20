module

public import PottsContinuity.Thm3.Prop4.CorridorWiredTubeError
public import PottsContinuity.Thm3.Prop4.StretchedSummability

/-!
# A fractional scale for the concrete tube corridor

Rounding the half-radius down gives an integral corridor width. The explicit
union error vanishes uniformly in the endpoints and the cluster weight.
-/

@[expose] public section

open Filter Topology

namespace PottsContinuity.Thm3.Prop4

/-- The half-radius floor is a positive admissible corridor scale. -/
theorem corridor_half_radius_floor_bounds {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : ε ≤ 1) (hr : 2 ≤ (n : ℝ)^ε) :
    1 ≤ ⌊(n : ℝ)^ε/2⌋₊ ∧ ⌊(n : ℝ)^ε/2⌋₊ ≤ n ∧
    4*(⌊(n : ℝ)^ε/2⌋₊ : ℝ)+1 ≤ 4*(n : ℝ)^ε := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrn : (n : ℝ)^ε ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR hε
  have hf := Nat.floor_le (show 0 ≤ (n : ℝ)^ε/2 by positivity)
  have hp : 0 < ⌊(n : ℝ)^ε/2⌋₊ := Nat.floor_pos.mpr (by linarith)
  refine ⟨by omega,Nat.floor_le_of_le (by linarith),by linarith⟩

/-- The rounded corridor error is bounded by a stretched exponential with a
polynomial prefactor, retaining the exact positive decay coefficient. -/
theorem corridor_half_radius_error_le {n : ℕ} (hn : 1 ≤ n)
    (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    (10*(n : ℝ)+2)*(⌊(n : ℝ)^ε/2⌋₊ : ℝ)*
        Real.exp (-c₀*((⌊(n : ℝ)^ε/2⌋₊ : ℝ)+1)^α) ≤
      6*(n : ℝ)^(1+ε)*Real.exp (-(c₀/2^α)*(n : ℝ)^(ε*α)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hr : 0 ≤ (n : ℝ)^ε := Real.rpow_nonneg hnpos.le _
  have hf := Nat.floor_le (show 0 ≤ (n : ℝ)^ε/2 by positivity)
  have hlt := Nat.lt_floor_add_one ((n : ℝ)^ε/2)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ)^ε/2) hlt.le hα.le
  have he : Real.exp (-c₀*((⌊(n : ℝ)^ε/2⌋₊ : ℝ)+1)^α) ≤
      Real.exp (-(c₀/2^α)*(n : ℝ)^(ε*α)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr hc₀.le)
    rw [Real.div_rpow hr (by norm_num), ← Real.rpow_mul hnpos.le] at hm
    convert hm using 1; ring
  have hpref : (10*(n : ℝ)+2)*(⌊(n : ℝ)^ε/2⌋₊ : ℝ) ≤ 6*(n : ℝ)^(1+ε) := by
    have h1 := mul_le_mul_of_nonneg_left hf (show 0 ≤ 10*(n : ℝ)+2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right (show 10*(n : ℝ)+2 ≤ 12*n by linarith) (show 0 ≤ (n : ℝ)^ε/2 by positivity)
    rw [Real.rpow_add hnpos,Real.rpow_one]
    nlinarith only [h1,h2]
  exact mul_le_mul hpref he (Real.exp_nonneg _) (by positivity)

/-- The explicit error bound vanishes for every positive fractional exponent. -/
theorem corridor_fractional_error_tendsto_zero (c₀ α ε : ℝ)
    (hc₀ : 0 < c₀) (hα : 0 < α) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => 6*(n : ℝ)^(1+ε)*
      Real.exp (-(c₀/2^α)*(n : ℝ)^(ε*α))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_stretched_exp_zero (1+ε) (c₀/2^α) (ε*α)
    (div_pos hc₀ (Real.rpow_pos_of_pos (by norm_num) _)) (mul_pos hε hα)).const_mul 6
  simpa only [mul_assoc,mul_zero] using h

end PottsContinuity.Thm3.Prop4
