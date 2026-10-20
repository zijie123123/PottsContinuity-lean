module

public import PottsContinuity.Thm3.Prop4.MaximalRecordSplitBound

/-!
# Uniform polynomial cost of the actual maximal-root touch comparison

The widened local scale is bounded by eight times the source scale. Closing
the original star contributes a parameter-only factor, retained explicitly.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- The inverse polynomial touch factor at the actual widened scale has the
uniform original-scale n^4 upper bound, including the smallest positive n. -/
theorem maximal_touch_denominator_le {n : ℕ} (hn : 1 ≤ n) :
    20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2 ≤ 81920*(n : ℝ)^4 := by
  have hk : ((4*n+4 : ℕ) : ℝ) ≤ 8*(n : ℝ) := by
    exact_mod_cast (show 4*n+4 ≤ 8*n by omega)
  calc
    _ = 20*((4*n+4 : ℕ) : ℝ)^4 := by ring
    _ ≤ 20*(8*(n : ℝ))^4 := by gcongr
    _ = _ := by ring

/-- Removing the actual polynomial touch and four-edge closing factors keeps
one explicit parameter-only coefficient and the original n^4 source scale. -/
theorem maximal_touch_star_cost_extract (θ : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (S K : ℝ) (hK : 0 ≤ K)
    (h : (1-edgeParameter θ)^4 *
      (1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2))*S ≤ K) :
    S ≤ (81920/(1-edgeParameter θ)^4)*(n : ℝ)^4*K := by
  have hc : 0 < (1-edgeParameter θ)^4 := pow_pos (one_sub_edgeParameter_pos θ) _
  have hk : (0 : ℝ) < ((4*n+4 : ℕ) : ℝ) := by positivity
  have hd : (0 : ℝ) < 20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2 := by positivity
  have hdiv : ((1-edgeParameter θ)^4*S)/
      (20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤ K := by
    convert h using 1; ring
  have hmul := (div_le_iff₀ hd).mp hdiv
  have hS : S ≤ K*(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2)/(1-edgeParameter θ)^4 := by
    apply (le_div_iff₀ hc).mpr
    nlinarith only [hmul]
  calc
    _ ≤ K*(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2)/(1-edgeParameter θ)^4 := hS
    _ ≤ K*(81920*(n : ℝ)^4)/(1-edgeParameter θ)^4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (maximal_touch_denominator_le hn) hK) hc.le
    _ = _ := by ring

end PottsContinuity.Thm3.Prop4
