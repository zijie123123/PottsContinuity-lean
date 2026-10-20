-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverExtremalDecayLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open Filter Topology

/-- The polynomially many vertices on the two extremal sheets are negligible against the
uniform exponential layer-avoidance rate. -/
theorem tendsto_parafermionicCover_extremalLayer_envelope :
    Tendsto (fun n : ℕ =>
      2 * (2 * (n : ℝ) + 1)^2 * Real.exp (-((n : ℝ) - 1) / 60))
      atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun n => (n : ℝ) / 60
  have hx : Tendsto x atTop atTop := by
    dsimp [x]
    exact tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 60)
  have h2 : Tendsto (fun n => x n ^ 2 * Real.exp (-x n)) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx
  have h1 : Tendsto (fun n => x n * Real.exp (-x n)) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx using 1
    ext n
    simp [pow_one]
  have h0 : Tendsto (fun n => Real.exp (-x n)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have hsum : Tendsto (fun n =>
      14400 * (x n ^ 2 * Real.exp (-x n)) +
        240 * (x n * Real.exp (-x n)) + Real.exp (-x n))
      atTop (𝓝 0) := by
    convert ((h2.const_mul 14400).add (h1.const_mul 240)).add h0 using 1; simp
  have hformula (n : ℕ) :
      2 * (2 * (n : ℝ) + 1)^2 * Real.exp (-((n : ℝ) - 1) / 60) =
        (2 * Real.exp (1 / 60)) *
          (14400 * (x n ^ 2 * Real.exp (-x n)) +
            240 * (x n * Real.exp (-x n)) + Real.exp (-x n)) := by
    have hn : (n : ℝ) = 60 * x n := by
      dsimp [x]
      ring
    rw [hn]
    have hexp : -((60 * x n) - 1) / 60 = -x n + 1 / 60 := by ring
    rw [hexp, Real.exp_add]
    ring
  convert hsum.const_mul (2 * Real.exp (1 / 60)) using 1
  · ext n
    exact hformula n
  · simp

end PottsContinuity.FKC.FiniteFK
