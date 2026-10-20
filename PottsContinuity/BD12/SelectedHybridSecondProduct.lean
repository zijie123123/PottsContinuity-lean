module

public import PottsContinuity.BD12.FixedOriginalHybridRegularity
public import PottsContinuity.BD12.OriginalPinBlockIntegralRecursion
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The product of separate V-expectations in the second Harris cross term.
First average original inputs after the query, then its current original input. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- The second Harris product averages to the product of original-law means.
No association or covariance conclusion is assumed; the two-stage original
averaging uses the actual block laws and selected-bit dependence. -/
theorem finiteSelectedHybrid_second_product_average
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅)
    (e : E) (hquery : finiteOriginalQueryAt w U t T ∅ = some e) :
    let ν := Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
    let A := fun W => ∫ v, f (finiteJointHybridEval w f (t + 1) W
      (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) ∂ν
    let B := fun W => ∫ v, (if e ∈ finiteJointHybridEval w f t W
      (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false then (1 : ℝ) else 0) ∂ν
    (∫ W, A W * B W ∂finiteOriginalPinBlock t (Fintype.card E - t) U) =
      finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun C => if e ∈ C then 1 else 0) := by
  let N := Fintype.card E
  let k := N - (t + 1)
  let ν := Measure.pi (fun _ : Fin N => finiteUnitUniform)
  let I := fun C : Finset E => if e ∈ C then (1 : ℝ) else 0
  let A := fun W => ∫ v, f (finiteJointHybridEval w f (t + 1) W (finiteSeedExtension N V v) T ∅ ∅ false) ∂ν
  let B := fun W => ∫ v, I (finiteJointHybridEval w f t W (finiteSeedExtension N V v) T ∅ ∅ false) ∂ν
  have hI01 : ∀ C, I C ∈ Set.Icc (0 : ℝ) 1 := by intro C; dsimp [I]; split_ifs <;> norm_num
  have ht : t < N := finiteOriginalQueryAt_lt_card w U t T ∅ e hquery
  have hindex : N - t = k + 1 := by dsimp [k]; omega
  have hAm : Measurable A := finiteJointHybridEval_product_integral_measurable w f f (t + 1) V T
  have hBm : Measurable B := finiteJointHybridEval_product_integral_measurable w f I t V T
  have hA01 (W : ℕ → ℝ) : A W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteJointHybridEval_product_integral_mem_Icc w f f hf01 (t + 1) W V T
  have hB01 (W : ℕ → ℝ) : B W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteJointHybridEval_product_integral_mem_Icc w f I hI01 t W V T
  have hAB01 (W : ℕ → ℝ) : A W * B W ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hA01 W).1 (hB01 W).1,
      (mul_le_mul_of_nonneg_right (hA01 W).2 (hB01 W).1).trans (by simpa using (hB01 W).2)⟩
  have hqueryu (u : ℝ) : finiteOriginalQueryAt w (Function.update U t u) t T ∅ = some e := by
    have heq := finiteOriginalQueryAt_congr_prefix w U (Function.update U t u) t
      (fun i hi => by rw [Function.update_of_ne (show i ≠ t by omega)]) T ∅
    exact heq.symm.trans hquery
  have htailB (u : ℝ) :
      (∫ W, B W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u)) = B (Function.update U t u) := by
    have h := finiteJointHybrid_original_bit_block_factor w f (Function.update U t u) V t k N
      T ∅ ∅ false e (hqueryu u) (fun _ => 1)
    simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  have htailAB (u : ℝ) :
      (∫ W, A W * B W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u)) =
        finitePinnedMean w ∅ ∅ f * B (Function.update U t u) := by
    have h := finiteJointHybrid_original_bit_block_factor w f (Function.update U t u) V t k N
      T ∅ ∅ false e (hqueryu u) A
    have hmean := finiteJointHybridEval_product_block_integral w f f hf01 (t + 1) (t + 1)
      (Function.update U t u) V (fun i => (U i, V i)) T (by omega) le_rfl
    change (∫ W, A W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u)) =
      finitePinnedMean w ∅ ∅ f at hmean
    change (∫ W, B W * A W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u)) =
      B (Function.update U t u) * ∫ W, A W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u) at h
    rw [hmean] at h
    calc
      _ = ∫ W, B W * A W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u) := by simp_rw [mul_comm]
      _ = _ := h.trans (mul_comm _ _)
  have hBmean : (∫ u, B (Function.update U t u) ∂finiteUnitUniform) = finitePinnedMean w ∅ ∅ I := by
    calc
      _ = ∫ u, ∫ W, B W ∂finiteOriginalPinBlock (t + 1) k (Function.update U t u) ∂finiteUnitUniform := by
        simp_rw [htailB]
      _ = ∫ W, B W ∂finiteOriginalPinBlock t (k + 1) U :=
        (finiteOriginalPinBlock_integral_succ t k U B hBm hB01).symm
      _ = _ := by
        have h := finiteJointHybridEval_product_block_integral w f I hI01 t t U V
          (fun i => (U i, V i)) T ht.le le_rfl
        change (∫ W, B W ∂finiteOriginalPinBlock t (N - t) U) = finitePinnedMean w ∅ ∅ I at h
        rw [hindex] at h
        exact h
  change (∫ W, A W * B W ∂finiteOriginalPinBlock t (N - t) U) = _
  rw [hindex, finiteOriginalPinBlock_integral_succ t k U (fun W => A W * B W) (hAm.mul hBm) hAB01]
  simp_rw [htailAB]
  rw [integral_const_mul, hBmean]

end
end PottsContinuity.BD12
