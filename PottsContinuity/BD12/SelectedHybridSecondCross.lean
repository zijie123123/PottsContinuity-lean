module

public import PottsContinuity.BD12.SelectedHybridSecondProduct
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! The second integrated Harris cross term, using the two-stage original-input
average of the actual separate replacement-input expectations. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- The second actual cross moment is bounded below by the product of original
means. The dependence at the current original input is integrated explicitly. -/
theorem finiteSelectedHybrid_second_cross_lower_bound
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅)
    (e : E) (hquery : finiteOriginalQueryAt w U t T ∅ = some e) :
    finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0) ≤
      ∫ W, ∫ v,
        f (finiteJointHybridEval w f (t + 1) W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) *
          (if e ∈ finiteJointHybridEval w f t W
            (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false then (1 : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
        ∂finiteOriginalPinBlock t (Fintype.card E - t) U := by
  let N := Fintype.card E
  let ν := Measure.pi (fun _ : Fin N => finiteUnitUniform)
  let μ := finiteOriginalPinBlock t (N - t) U
  let I := fun A : Finset E => if e ∈ A then (1 : ℝ) else 0
  let Y := fun s (W : ℕ → ℝ) (v : Fin N → ℝ) =>
    finiteJointHybridEval w f s W (finiteSeedExtension N V v) T ∅ ∅ false
  let A := fun W => ∫ v, f (Y (t + 1) W v) ∂ν
  let B := fun W => ∫ v, I (Y t W v) ∂ν
  let C := fun W => ∫ v, f (Y (t + 1) W v) * I (Y t W v) ∂ν
  have hI01 : ∀ D, I D ∈ Set.Icc (0 : ℝ) 1 := by intro D; dsimp [I]; split_ifs <;> norm_num
  have hIm : Monotone I := by
    intro D F hDF
    dsimp only [I]
    by_cases hd : e ∈ D
    · simp only [ite_eq_left hd, ite_eq_left (hDF hd), le_refl]
    · simp only [ite_eq_right hd]; split_ifs <;> norm_num
  have hinput : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) => (z.1, finiteSeedExtension N V z.2)) :=
    measurable_fst.prodMk ((finiteSeedExtension_measurable N V).comp measurable_snd)
  have hY (s : ℕ) : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) => Y s z.1 z.2) :=
    (finiteJointHybridEval_measurable w f s T ∅ ∅ false).comp hinput
  have hFm : Measurable f := measurable_of_finite f
  have hIms : Measurable I := measurable_of_finite I
  have hproduct : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) =>
      f (Y (t + 1) z.1 z.2) * I (Y t z.1 z.2)) :=
    (hFm.comp (hY (t + 1))).mul (hIms.comp (hY t))
  have hpoint01 (W : ℕ → ℝ) (v : Fin N → ℝ) :
      f (Y (t + 1) W v) * I (Y t W v) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hf01 _).1 (hI01 _).1,
      (mul_le_mul_of_nonneg_right (hf01 _).2 (hI01 _).1).trans (by simpa using (hI01 (Y t W v)).2)⟩
  have hCm : Measurable C := hproduct.stronglyMeasurable.integral_prod_right'.measurable
  have hC01 (W : ℕ → ℝ) : C W ∈ Set.Icc (0 : ℝ) 1 := by
    have hm : Measurable (fun v : Fin N → ℝ => f (Y (t + 1) W v) * I (Y t W v)) :=
      hproduct.comp measurable_prodMk_left
    have hi := integrable_of_unit_bounds ν hm (hpoint01 W)
    refine ⟨integral_nonneg (fun v => (hpoint01 W v).1), ?_⟩
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const (1 : ℝ)) (fun v => (hpoint01 W v).2)
  have hAm : Measurable A := finiteJointHybridEval_product_integral_measurable w f f (t + 1) V T
  have hBm : Measurable B := finiteJointHybridEval_product_integral_measurable w f I t V T
  have hA01 (W : ℕ → ℝ) : A W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteJointHybridEval_product_integral_mem_Icc w f f hf01 (t + 1) W V T
  have hB01 (W : ℕ → ℝ) : B W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteJointHybridEval_product_integral_mem_Icc w f I hI01 t W V T
  have hlefti := integrable_of_unit_bounds μ (hAm.mul hBm) (fun W =>
    ⟨mul_nonneg (hA01 W).1 (hB01 W).1,
      (mul_le_mul_of_nonneg_right (hA01 W).2 (hB01 W).1).trans (by simpa using (hB01 W).2)⟩)
  have hrighti := integrable_of_unit_bounds μ hCm hC01
  have hle (W : ℕ → ℝ) : A W * B W ≤ C W :=
    finiteJointHybrids_positive_association w hw f f I (t + 1) t N W V
      T ∅ ∅ ∅ false hFm hIms hf hIm hf01 hI01
  have h := integral_mono hlefti hrighti hle
  have havg := finiteSelectedHybrid_second_product_average w f hf01 U V t T e hquery
  change (∫ W, A W * B W ∂μ) = _ at havg
  change (∫ W, A W * B W ∂μ) ≤ ∫ W, C W ∂μ at h
  rw [havg] at h
  exact h

end
end PottsContinuity.BD12
