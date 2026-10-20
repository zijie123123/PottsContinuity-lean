module

public import PottsContinuity.BD12.SelectedHybridFirstCross
public import PottsContinuity.BD12.SelectedHybridSecondCross
public import PottsContinuity.BD12.SelectedHybridSwitch
public import PottsContinuity.BD12.HybridPairMoments
public import PottsContinuity.BD12.IntegralFourTerms
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual adjacent-hybrid switch cost is bounded by twice the original
covariance at the adaptively selected edge. Both original-input and replacement
input averages are the concrete finite product constructions. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- DRT's selected-query covariance estimate. The edge is selected by the actual
original exploration at time t; its strict prefix is retained in the averaging.
No hybrid moment, association or covariance estimate is supplied as a premise. -/
theorem finiteSelectedHybrid_switch_cost_le_twice_covariance
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅)
    (e : E) (hquery : finiteOriginalQueryAt w U t T ∅ = some e) :
    (∫ W, ∫ v,
      |f (finiteJointHybridEval w f (t + 1) W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) -
        f (finiteJointHybridEval w f t W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)|
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
      ∂finiteOriginalPinBlock t (Fintype.card E - t) U) ≤
    2 * (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
      finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0)) := by
  let N := Fintype.card E
  let ν := Measure.pi (fun _ : Fin N => finiteUnitUniform)
  let μ := finiteOriginalPinBlock t (N - t) U
  let I := fun A : Finset E => if e ∈ A then (1 : ℝ) else 0
  let Y := fun s (W : ℕ → ℝ) (v : Fin N → ℝ) =>
    finiteJointHybridEval w f s W (finiteSeedExtension N V v) T ∅ ∅ false
  let K := fun s r (W : ℕ → ℝ) => ∫ v, f (Y s W v) * I (Y r W v) ∂ν
  let C := fun W => ∫ v, |f (Y (t + 1) W v) - f (Y t W v)| ∂ν
  have hI01 : ∀ A, I A ∈ Set.Icc (0 : ℝ) 1 := by intro A; dsimp [I]; split_ifs <;> norm_num
  have hprod01 (A B : Finset E) : f A * I B ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg (hf01 A).1 (hI01 B).1,
      (mul_le_mul_of_nonneg_right (hf01 A).2 (hI01 B).1).trans (by simpa using (hI01 B).2)⟩
  have hKm (s r : ℕ) : Measurable (K s r) :=
    finiteHybridPair_product_integral_measurable w f (fun A => f A.1 * I A.2) s r V T
  have hK01 (s r : ℕ) (W : ℕ → ℝ) : K s r W ∈ Set.Icc (0 : ℝ) 1 :=
    finiteHybridPair_product_integral_mem_Icc w f (fun A => f A.1 * I A.2)
      (fun A => hprod01 A.1 A.2) s r W V T
  have hKi (s r : ℕ) : Integrable (K s r) μ :=
    integrable_of_unit_bounds μ (hKm s r) (hK01 s r)
  have hinner (W : ℕ → ℝ) (hqueryW : finiteOriginalQueryAt w W t T ∅ = some e) :
      C W = K (t + 1) (t + 1) W + K t t W - K (t + 1) t W - K t (t + 1) W := by
    have hinput : Measurable (fun v : Fin N → ℝ => (W, finiteSeedExtension N V v)) :=
      measurable_const.prodMk (finiteSeedExtension_measurable N V)
    have hY (s : ℕ) : Measurable (Y s W) :=
      (finiteJointHybridEval_measurable w f s T ∅ ∅ false).comp hinput
    have hi (s r : ℕ) : Integrable (fun v => f (Y s W v) * I (Y r W v)) ν :=
      integrable_of_unit_bounds ν
        (((measurable_of_finite f).comp (hY s)).mul ((measurable_of_finite I).comp (hY r)))
        (fun v => hprod01 _ _)
    exact integral_four_term_identity ν _ _ _ _ _ (hi (t + 1) (t + 1)) (hi t t)
      (hi (t + 1) t) (hi t (t + 1)) (Filter.Eventually.of_forall (fun v =>
        finiteSelectedHybrids_switch_identity w hw f f hf W (finiteSeedExtension N V v)
          t T ∅ ∅ false e hqueryW))
  have heq : (∫ W, C W ∂μ) = (∫ W, K (t + 1) (t + 1) W ∂μ) +
      (∫ W, K t t W ∂μ) - (∫ W, K (t + 1) t W ∂μ) - (∫ W, K t (t + 1) W ∂μ) := by
    apply integral_four_term_identity μ C _ _ _ _ (hKi (t + 1) (t + 1)) (hKi t t)
      (hKi (t + 1) t) (hKi t (t + 1))
    filter_upwards [finiteOriginalPinBlock_ae_past t (N - t) U] with W hW
    apply hinner W
    exact (finiteOriginalQueryAt_congr_prefix w U W t (fun i hi => (hW i hi).symm) T ∅).symm.trans hquery
  have ht : t < N := finiteOriginalQueryAt_lt_card w U t T ∅ e hquery
  have hdiag (s : ℕ) (hs : t ≤ s) :
      (∫ W, K s s W ∂μ) = finitePinnedMean w ∅ ∅ (fun A => f A * I A) :=
    finiteJointHybridEval_product_block_integral w f (fun A => f A * I A)
      (fun A => hprod01 A A) t s U V (fun i => (U i, V i)) T ht.le hs
  have hfirst := finiteSelectedHybrid_first_cross_lower_bound w hw f hf hf01 U V t T e hquery
  have hsecond := finiteSelectedHybrid_second_cross_lower_bound w hw f hf hf01 U V t T e hquery
  change finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ I ≤ ∫ W, K t (t + 1) W ∂μ at hfirst
  change finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ I ≤ ∫ W, K (t + 1) t W ∂μ at hsecond
  change (∫ W, C W ∂μ) ≤ _
  rw [heq, hdiag (t + 1) (by omega), hdiag t le_rfl]
  change _ ≤ 2 * (finitePinnedMean w ∅ ∅ (fun A => f A * I A) -
    finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ I)
  linarith only [hfirst, hsecond]

end
end PottsContinuity.BD12
