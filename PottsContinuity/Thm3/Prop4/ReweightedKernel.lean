module

public import PottsContinuity.Thm3.Prop4.AnalyticSum
public import Mathlib.Tactic

/-!
# Extracting the product factor from the source convolution

DCST, TeX lines 1775–1785. The kernel retains both the diagonal and the
polynomially weighted off-diagonal terms of the source expression.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The actual reweighted source summand, including the sequence factors. -/
noncomputable def prop4ReweightedKernel (C c ε β : ℝ) (u : ℕ → ℝ) (m : ℕ) : ℝ := by
  classical
  exact C*(m : ℝ)^4*(Real.exp (c*(m : ℝ)^ε)*Real.exp (-2*(m : ℝ)^β)*(u m)^2+
    c*(m : ℝ)^6*∑ k ∈ Finset.range (2*m+1),
      if (m : ℝ)^ε ≤ k ∧ (m : ℝ)^ε ≤ (2*m-k : ℕ) then
        Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β))*u k*u (2*m-k) else 0)

/-- The source summand is nonnegative at every index. -/
theorem prop4ReweightedKernel_nonneg (C c ε β : ℝ) (u : ℕ → ℝ)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hu : ∀ n, 0 ≤ u n) (m : ℕ) :
    0 ≤ prop4ReweightedKernel C c ε β u m := by
  classical
  unfold prop4ReweightedKernel
  apply mul_nonneg (by positivity)
  apply add_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (hu k)) (hu (2*m-k))
  · exact le_rfl

/-- A common admissible product bound factors out of each entire source term. -/
theorem prop4ReweightedKernel_le_product (C c ε β B : ℝ) (u : ℕ → ℝ)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hprod : ∀ k l : ℕ, (n : ℝ)^ε ≤ k → (n : ℝ)^ε ≤ l →
      2*n ≤ k+l → u k*u l ≤ B) :
    prop4ReweightedKernel C c ε β u m ≤ B*prop4Kernel C c ε β m := by
  classical
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hn.trans hnm
  have hnmε : (n : ℝ)^ε ≤ (m : ℝ)^ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnm) hε
  have hmε : (m : ℝ)^ε ≤ m := by
    simpa using Real.rpow_le_rpow_of_exponent_le hm1 hε1
  have hdiag : (u m)^2 ≤ B := by
    simpa only [pow_two] using hprod m m (hnmε.trans hmε)
      (hnmε.trans hmε) (by omega)
  have hsplit : (∑ k ∈ Finset.range (2*m+1),
      if (m : ℝ)^ε ≤ k ∧ (m : ℝ)^ε ≤ (2*m-k : ℕ) then
        Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β))*u k*u (2*m-k) else 0) ≤
      B*prop4SplitWeight ε β m := by
    unfold prop4SplitWeight
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with h
    · have hk2 : k ≤ 2*m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hp := hprod k (2*m-k) (hnmε.trans h.1) (hnmε.trans h.2) (by omega)
      calc
        _ = Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β))*(u k*u (2*m-k)) := by ring
        _ ≤ Real.exp (-((k : ℝ)^β+((2*m-k : ℕ) : ℝ)^β))*B :=
          mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
        _ = _ := by ring
    · simp
  unfold prop4ReweightedKernel prop4Kernel
  calc
    _ ≤ C*(m : ℝ)^4*(Real.exp (c*(m : ℝ)^ε)*Real.exp (-2*(m : ℝ)^β)*B+
        c*(m : ℝ)^6*(B*prop4SplitWeight ε β m)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hdiag (by positivity))
        (mul_le_mul_of_nonneg_left hsplit (by positivity))
    _ = _ := by ring

end PottsContinuity.Thm3.Prop4
