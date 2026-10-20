module

public import PottsContinuity.Thm3.Prop4.PairKernel
public import PottsContinuity.Thm3.RSW.OneArm
public import PottsContinuity.Thm3.RSW.SquarePair

/-!
# Finite-scale completion of Lemma 7

DCST, TeX line 1759, the final step of the proof of Lemma 7. The source only
proves the tube estimate eventually. Positive actual one-arm probabilities
allow the diagonal penalty to cover every omitted finite scale.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open MeasureTheory

/-- At finitely many positive indices, a large enough diagonal exponential
penalty compensates any strictly positive sequence. -/
theorem finite_diagonal_penalty (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ε : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → n ≤ N →
      1 ≤ Real.exp (C*(n : ℝ)^ε)*(a n)^2 := by
  classical
  let s := Finset.Icc 1 N
  let g : ℕ → ℝ := fun n => max 0 (-2*Real.log (a n))/(n : ℝ)^ε
  have hg : ∀ n, 0 ≤ g n := fun n => div_nonneg (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) ε)
  let C := (∑ n ∈ s, g n)+1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun n _ => hg n)) zero_lt_one
  refine ⟨C,hC,?_⟩
  intro n hn hnN
  have hnε : 0 < (n : ℝ)^ε := Real.rpow_pos_of_pos (by exact_mod_cast hn) ε
  have hterm : g n ≤ ∑ i ∈ s, g i := Finset.single_le_sum (fun i _ => hg i) (Finset.mem_Icc.mpr ⟨hn,hnN⟩)
  have hdiv : -2*Real.log (a n)/(n : ℝ)^ε ≤ C :=
    (div_le_div_of_nonneg_right (le_max_right _ _) hnε.le).trans (hterm.trans (by dsimp [C]; linarith))
  have hlog := (div_le_iff₀ hnε).mp hdiv
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (C*(n : ℝ)^ε+Real.log (a n)+Real.log (a n)) :=
      Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_add,Real.exp_add,Real.exp_log (ha n)]; ring

/-- Actual square-pair probabilities are bounded by one. -/
theorem maxSquarePairProbability_le_one (θ : PD.FK.Parameters) (m : ℕ) :
    RSW.maxSquarePairProbability θ m ≤ 1 := by
  apply RSW.maxSquarePairProbability_le
  intro i j
  unfold RSW.squarePairProbability RSW.finiteBoundaryEventProbability
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using prob_le_one)

/-- Increasing the nonnegative penalty coefficient increases the exact pair
expression, including its separate finite convolution. -/
theorem prop4PairKernel_mono_coefficient (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ε c C : ℝ) (hcC : c ≤ C) (m : ℕ) :
    prop4PairKernel c ε a m ≤ prop4PairKernel C ε a m := by
  classical
  unfold prop4PairKernel
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg (Nat.cast_nonneg m) ε))
  · apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcC (pow_nonneg (Nat.cast_nonneg m) _))
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact mul_nonneg (ha _) (ha _)
    · exact le_rfl

/-- The diagonal is one of the two nonnegative pieces of the exact pair bound. -/
theorem diagonal_le_prop4PairKernel (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ε c : ℝ) (hc : 0 ≤ c) (m : ℕ) :
    Real.exp (c*(m : ℝ)^ε)*(a m)^2 ≤ prop4PairKernel c ε a m := by
  classical
  unfold prop4PairKernel
  apply le_add_of_nonneg_right
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (ha _) (ha _)
  · exact le_rfl

end PottsContinuity.Thm3.Prop4
