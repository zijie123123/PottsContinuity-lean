module

public import PottsContinuity.Thm3.Prop4.ReweightedKernel
public import Mathlib.Tactic

/-!
# The Lemma-7 square-pair expression and its exact reweighting

DCST, equations (24), (29)–(32), and TeX lines 1775–1782. This numerical
expression keeps the diagonal penalty separate from the split-arm term.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The actual right-hand expression in the square-pair estimate, before
multiplication by the exterior-circuit polynomial. -/
noncomputable def prop4PairKernel (c ε : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ := by
  classical
  exact Real.exp (c*(m : ℝ)^ε)*(a m)^2 + c*(m : ℝ)^6*
    ∑ k ∈ Finset.range (2*m+1),
      if (m : ℝ)^ε ≤ k ∧ (m : ℝ)^ε ≤ (2*m-k : ℕ) then a k*a (2*m-k) else 0

/-- The pair expression is nonnegative at every index. -/
theorem prop4PairKernel_nonneg (c ε : ℝ) (a : ℕ → ℝ)
    (hc : 0 ≤ c) (ha : ∀ n, 0 ≤ a n) (m : ℕ) : 0 ≤ prop4PairKernel c ε a m := by
  classical
  unfold prop4PairKernel
  apply add_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (ha _) (ha _)
  · exact le_rfl

/-- Exact cancellation of the exponential reweighting in every source term. -/
theorem prop4ReweightedKernel_eq_pairKernel (C c ε β : ℝ) (a : ℕ → ℝ) (m : ℕ) :
    prop4ReweightedKernel C c ε β (fun k => Real.exp ((k : ℝ)^β)*a k) m =
      C*(m : ℝ)^4*prop4PairKernel c ε a m := by
  classical
  have hexp (x y : ℝ) : Real.exp (-(x+y))*Real.exp x*Real.exp y = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 2; ring
  have hdiag : Real.exp (-2*(m : ℝ)^β)*
      (Real.exp ((m : ℝ)^β)*a m)^2 = (a m)^2 := by
    calc
      _ = (Real.exp (-((m : ℝ)^β+(m : ℝ)^β))*
        Real.exp ((m : ℝ)^β)*Real.exp ((m : ℝ)^β))*(a m)^2 := by ring_nf
      _ = _ := by rw [hexp, one_mul]
  unfold prop4ReweightedKernel prop4PairKernel
  rw [mul_assoc (Real.exp _) (Real.exp _) _, hdiag]
  congr 2
  apply congrArg (fun s : ℝ => c*(m : ℝ)^6*s)
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · calc
      _ = (Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β))*
          Real.exp ((k : ℝ)^β)*Real.exp (((2*m-k : ℕ) : ℝ)^β))*(a k*a (2*m-k)) := by ring
      _ = _ := by rw [hexp, one_mul]
  · rfl

end PottsContinuity.Thm3.Prop4
