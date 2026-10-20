module

public import PottsContinuity.BD12.FixedOriginalHybridRegularity
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! The first integrated Harris cross term in DRT's covariance switch estimate:
the replaced selected bit has its original-law mean pointwise in fixed U. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Average the cross term f(Y^t)*Y^{t+1}_e over the remaining original inputs
and all replacement inputs. Its lower bound is the product of original means;
Harris, the actual selected-bit mean and the block tower are all discharged. -/
theorem finiteSelectedHybrid_first_cross_lower_bound
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅)
    (e : E) (hquery : finiteOriginalQueryAt w U t T ∅ = some e) :
    finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0) ≤
      ∫ W, ∫ v,
        f (finiteJointHybridEval w f t W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) *
          (if e ∈ finiteJointHybridEval w f (t + 1) W
            (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false then (1 : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
        ∂finiteOriginalPinBlock t (Fintype.card E - t) U := by
  let N := Fintype.card E
  let ν := Measure.pi (fun _ : Fin N => finiteUnitUniform)
  let μ := finiteOriginalPinBlock t (N - t) U
  let I := fun A : Finset E => if e ∈ A then (1 : ℝ) else 0
  let Y := fun s (W : ℕ → ℝ) (v : Fin N → ℝ) =>
    finiteJointHybridEval w f s W (finiteSeedExtension N V v) T ∅ ∅ false
  let B := fun W => ∫ v, f (Y t W v) ∂ν
  let C := fun W => ∫ v, f (Y t W v) * I (Y (t + 1) W v) ∂ν
  let p := finitePinnedMean w ∅ ∅ I
  have hI01 : ∀ A, I A ∈ Set.Icc (0 : ℝ) 1 := by intro A; dsimp [I]; split_ifs <;> norm_num
  have hIm : Monotone I := by
    intro A D hAD
    dsimp only [I]
    by_cases ha : e ∈ A
    · simp only [ite_eq_left ha, ite_eq_left (hAD ha), le_refl]
    · simp only [ite_eq_right ha]; split_ifs <;> norm_num
  have hinput : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) => (z.1, finiteSeedExtension N V z.2)) :=
    measurable_fst.prodMk ((finiteSeedExtension_measurable N V).comp measurable_snd)
  have hY (s : ℕ) : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) => Y s z.1 z.2) :=
    (finiteJointHybridEval_measurable w f s T ∅ ∅ false).comp hinput
  have hFm : Measurable f := measurable_of_finite f
  have hIms : Measurable I := measurable_of_finite I
  have hproduct : Measurable (fun z : (ℕ → ℝ) × (Fin N → ℝ) =>
      f (Y t z.1 z.2) * I (Y (t + 1) z.1 z.2)) :=
    (hFm.comp (hY t)).mul (hIms.comp (hY (t + 1)))
  have hpoint01 (W : ℕ → ℝ) (v : Fin N → ℝ) :
      f (Y t W v) * I (Y (t + 1) W v) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hf01 _).1 (hI01 _).1,
      (mul_le_mul_of_nonneg_right (hf01 _).2 (hI01 _).1).trans (by simpa using (hI01 (Y (t + 1) W v)).2)⟩
  have hCm : Measurable C := hproduct.stronglyMeasurable.integral_prod_right'.measurable
  have hC01 (W : ℕ → ℝ) : C W ∈ Set.Icc (0 : ℝ) 1 := by
    have hm : Measurable (fun v : Fin N → ℝ => f (Y t W v) * I (Y (t + 1) W v)) :=
      hproduct.comp measurable_prodMk_left
    have hi := integrable_of_unit_bounds ν hm (hpoint01 W)
    refine ⟨integral_nonneg (fun v => (hpoint01 W v).1), ?_⟩
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const (1 : ℝ)) (fun v => (hpoint01 W v).2)
  have hBm : Measurable B := finiteJointHybridEval_product_integral_measurable w f f t V T
  have hB01 (W : ℕ → ℝ) : B W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteJointHybridEval_product_integral_mem_Icc w f f hf01 t W V T
  have hp : p ∈ Set.Icc (0 : ℝ) 1 := by
    have h := finiteJointHybridEval_product_integral_mem_Icc w f I hI01 (t + 1) U V T
    rw [finiteSelectedHybrid_replaced_bit_mean w f U V t T e hquery] at h
    exact h
  have hlefti := integrable_of_unit_bounds μ (hBm.mul_const p) (fun W =>
    ⟨mul_nonneg (hB01 W).1 hp.1,
      (mul_le_mul_of_nonneg_right (hB01 W).2 hp.1).trans (by simpa using hp.2)⟩)
  have hrighti := integrable_of_unit_bounds μ hCm hC01
  have hle : ∀ᵐ W ∂μ, B W * p ≤ C W := by
    filter_upwards [finiteOriginalPinBlock_ae_past t (N - t) U] with W hW
    have hqueryW : finiteOriginalQueryAt w W t T ∅ = some e :=
      (finiteOriginalQueryAt_congr_prefix w U W t (fun i hi => (hW i hi).symm) T ∅).symm.trans hquery
    have hh := finiteJointHybrids_positive_association w hw f f I t (t + 1) N W V
      T ∅ ∅ ∅ false hFm hIms hf hIm hf01 hI01
    have hbit := finiteSelectedHybrid_replaced_bit_mean w f W V t T e hqueryW
    dsimp only at hh
    rw [hbit] at hh
    exact hh
  have h := integral_mono_ae hlefti hrighti hle
  rw [integral_mul_const] at h
  have havg := finiteJointHybridEval_product_block_integral w f f hf01 t t U V
    (fun i => (U i, V i)) T (finiteOriginalQueryAt_lt_card w U t T ∅ e hquery).le le_rfl
  change (∫ W, B W ∂μ) = finitePinnedMean w ∅ ∅ f at havg
  rw [havg] at h
  exact h

end
end PottsContinuity.BD12
