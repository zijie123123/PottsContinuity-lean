module

public import PottsContinuity.BD12.AdaptiveHybridQuery
public import PottsContinuity.BD12.OriginalPinBlockTower
public import PottsContinuity.BD12.JointHybridAssociation
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual selected-edge hybrid bits depend on the short original prefixes
used by DRT. Their replacement-uniform expectations can therefore be held fixed
when averaging the remaining original input block. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Once its edge is selected by the original exploration, the replaced bit of
the FINAL hybrid depends on the strict original prefix only. -/
theorem finiteJointHybrid_selected_replaced_congr_prefix
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U U' V : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i < t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e) :
    (if e ∈ finiteJointHybridEval w f (t + 1) U V T HX HY stopped then (1 : ℝ) else 0) =
    (if e ∈ finiteJointHybridEval w f (t + 1) U' V T HX HY stopped then (1 : ℝ) else 0) := by
  have hquery' : finiteOriginalQueryAt w U' t T HX = some e :=
    (finiteOriginalQueryAt_congr_prefix w U U' t hU T HX).symm.trans hquery
  have h := finiteHybridQueryAt_replaced_congr_prefix w f U U' V t hU T HX HY stopped
  rw [finiteHybridQueryAt_eq_final, finiteHybridQueryAt_eq_final,
    hquery, hquery', Option.map_some, Option.map_some] at h
  have hb := congrArg Prod.snd (Option.some.inj h)
  have hmem := Bool.eq_iff_iff.mp hb
  simp only [decide_eq_true_eq] at hmem
  simp only [hmem]

/-- For the preceding hybrid, the original prefix including the current input
suffices for its FINAL bit at the selected edge. -/
theorem finiteJointHybrid_selected_original_congr_prefix
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U U' V : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i ≤ t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e) :
    (if e ∈ finiteJointHybridEval w f t U V T HX HY stopped then (1 : ℝ) else 0) =
    (if e ∈ finiteJointHybridEval w f t U' V T HX HY stopped then (1 : ℝ) else 0) := by
  have hquery' : finiteOriginalQueryAt w U' t T HX = some e :=
    (finiteOriginalQueryAt_congr_prefix w U U' t (fun i hi => hU i hi.le) T HX).symm.trans hquery
  have h := finiteHybridQueryAt_original_congr_prefix w f U U' V t hU T HX HY stopped
  rw [finiteHybridQueryAt_eq_final, finiteHybridQueryAt_eq_final,
    hquery, hquery', Option.map_some, Option.map_some] at h
  have hb := congrArg Prod.snd (Option.some.inj h)
  have hmem := Bool.eq_iff_iff.mp hb
  simp only [decide_eq_true_eq] at hmem
  simp only [hmem]

/-- The replaced selected-bit V-expectation is an actual past-dependent factor
under averaging of the original inputs from t onwards. No prefix-dependence
premise is supplied: it is proved from the exploration and final-bit identity. -/
theorem finiteJointHybrid_replaced_bit_block_factor
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U background : ℕ → ℝ) (t k n : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e)
    (G : (ℕ → ℝ) → ℝ) :
    let ν := Measure.pi (fun _ : Fin n => finiteUnitUniform)
    let B := fun W => ∫ v, (if e ∈ finiteJointHybridEval w f (t + 1) W
      (finiteSeedExtension n background v) T HX HY stopped then (1 : ℝ) else 0) ∂ν
    (∫ W, B W * G W ∂finiteOriginalPinBlock t k U) =
      B U * ∫ W, G W ∂finiteOriginalPinBlock t k U := by
  apply finiteOriginalPinBlock_integral_past_factor
  intro W hW
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v =>
    finiteJointHybrid_selected_replaced_congr_prefix w f W U
      (finiteSeedExtension n background v) t hW T HX HY stopped e
      ((finiteOriginalQueryAt_congr_prefix w U W t
        (fun i hi => (hW i hi).symm) T HX).symm.trans hquery))

/-- The preceding hybrid bit can likewise be held fixed while averaging all
original inputs strictly after the current one. -/
theorem finiteJointHybrid_original_bit_block_factor
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U background : ℕ → ℝ) (t k n : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e)
    (G : (ℕ → ℝ) → ℝ) :
    let ν := Measure.pi (fun _ : Fin n => finiteUnitUniform)
    let B := fun W => ∫ v, (if e ∈ finiteJointHybridEval w f t W
      (finiteSeedExtension n background v) T HX HY stopped then (1 : ℝ) else 0) ∂ν
    (∫ W, B W * G W ∂finiteOriginalPinBlock (t + 1) k U) =
      B U * ∫ W, G W ∂finiteOriginalPinBlock (t + 1) k U := by
  apply finiteOriginalPinBlock_integral_past_factor
  intro W hW
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v =>
    finiteJointHybrid_selected_original_congr_prefix w f W U
      (finiteSeedExtension n background v) t (fun i hi => hW i (by omega)) T HX HY stopped e
      ((finiteOriginalQueryAt_congr_prefix w U W t
        (fun i hi => (hW i (by omega)).symm) T HX).symm.trans hquery))

end
end PottsContinuity.BD12
