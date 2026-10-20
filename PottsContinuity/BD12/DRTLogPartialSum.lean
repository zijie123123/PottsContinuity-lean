module

public import PottsContinuity.BD12.DRTPartialSumDecay
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The finite logarithmic telescoping bound in DRT's scalar technical lemma.
The denominators are the actual partial sums, positive from the zeroth term. -/

@[expose] public section

namespace PottsContinuity.BD12

/-- The elementary logarithmic increment bound at a positive partial sum. -/
theorem drt_log_increment_le_ratio (s b : ℝ) (hs : 0 < s) (hb : 0 ≤ b) :
    Real.log (s + b) - Real.log s ≤ b / s := by
  have hsum : 0 < s + b := add_pos_of_pos_of_nonneg hs hb
  have h := Real.log_le_sub_one_of_pos (div_pos hsum hs)
  rw [Real.log_div hsum.ne' hs.ne', add_div, div_self hs.ne'] at h
  linarith only [h]

/-- The actual partial sums are positive for every n>=1 when the zeroth
summand is positive and all summands are nonnegative. -/
theorem drtPartialSum_pos (F : ℕ → ℝ → ℝ) (x : ℝ)
    (hF : ∀ k, 0 ≤ F k x) (hzero : 0 < F 0 x) (n : ℕ) (hn : 1 ≤ n) :
    0 < drtPartialSum F n x := by
  have hle : F 0 x ≤ drtPartialSum F n x :=
    Finset.single_le_sum (fun k _ => hF k) (show 0 ∈ Finset.range n by simp; omega)
  exact hzero.trans_le hle

/-- Source bound sum_{i=1}^n F_i/Sigma_i >= log Sigma_{n+1}-log Sigma_1.
This is finite and exact; no convergence or averaged-limit assertion is assumed. -/
theorem drt_log_partial_sum_le_sum_ratio (F : ℕ → ℝ → ℝ) (x : ℝ)
    (hF : ∀ k, 0 ≤ F k x) (hzero : 0 < F 0 x) (n : ℕ) :
    Real.log (drtPartialSum F (n + 1) x) - Real.log (drtPartialSum F 1 x) ≤
      ∑ i ∈ Finset.range n, F (i + 1) x / drtPartialSum F (i + 1) x := by
  have hstep (i : ℕ) :
      Real.log (drtPartialSum F (i + 2) x) - Real.log (drtPartialSum F (i + 1) x) ≤
        F (i + 1) x / drtPartialSum F (i + 1) x := by
    have hnext : drtPartialSum F (i + 2) x = drtPartialSum F (i + 1) x + F (i + 1) x :=
      Finset.sum_range_succ (fun k => F k x) (i + 1)
    rw [hnext]
    exact drt_log_increment_le_ratio _ _ (drtPartialSum_pos F x hF hzero _ (by omega)) (hF (i + 1))
  have htel : (∑ i ∈ Finset.range n,
      (Real.log (drtPartialSum F (i + 2) x) - Real.log (drtPartialSum F (i + 1) x))) =
      Real.log (drtPartialSum F (n + 1) x) - Real.log (drtPartialSum F 1 x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [← htel]
  exact Finset.sum_le_sum (fun i _ => hstep i)

end PottsContinuity.BD12
