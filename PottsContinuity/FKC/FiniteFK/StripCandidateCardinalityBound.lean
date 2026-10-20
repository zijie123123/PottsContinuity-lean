-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/StripCandidateCardinalityBound.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- Real form of the candidate-count arithmetic for the nondegenerate strip
regime. -/
theorem stripCandidate_cardinality_bound_real
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (hm : 2 ≤ m) :
    2 * (2 * (n : ℝ) * (m : ℝ) + 1) * ((n : ℝ) + 1) ≤
      5 * (n : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hmR : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have hA : 0 ≤ (n : ℝ) ^ 2 * (m : ℝ) * ((m : ℝ) - 2) := by positivity
  have hB : 0 ≤ (n : ℝ) * (m : ℝ) * ((n : ℝ) - 1) := by positivity
  have hC : 0 ≤ (n : ℝ) * ((m : ℝ) - 1) - 1 := by
    have hnm2 : 0 ≤ (n : ℝ) * ((m : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  nlinarith [hA, hB, hC, hnmR]

/-- Reciprocal candidate probability is at least the published reciprocal
`1 / (5 n^2 m^2)` in the nondegenerate strip regime. The case `n=m=1` is not
covered by these hypotheses. -/
theorem stripCandidate_reciprocal_bound
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (hm : 2 ≤ m) :
    (1 : ℝ) / (5 * (n : ℝ) ^ 2 * (m : ℝ) ^ 2) ≤
      1 / (2 * (2 * (n : ℝ) * (m : ℝ) + 1) * ((n : ℝ) + 1)) := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact stripCandidate_cardinality_bound_real hn hnm hm

end PottsContinuity.FKC.FiniteFK
