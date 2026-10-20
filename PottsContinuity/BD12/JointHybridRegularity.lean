module

public import PottsContinuity.BD12.JointHybridEvaluation
public import PottsContinuity.BD12.FiniteMonotoneSampler

/-! Measurability and replacement-seed monotonicity of the common-space DRT
hybrids. Their original reveal order and stopping rule remain fixed when V
varies; no assumption about the hybrid output is used. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section

/-- Measurable selection from finitely many measurable maps. -/
theorem measurable_finite_selection {ι Ω Ξ : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (F : ι → Ω → Ξ)
    (hF : ∀ i, Measurable (F i)) (s : Ω → ι) (hs : Measurable s) :
    Measurable (fun z => F (s z) z) :=
  (measurable_from_prod_countable_right (f := fun p : ι × Ω => F p.1 p.2) hF).comp (hs.prodMk measurable_id)

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Measurability of the original sample in its full real seed stream. -/
theorem finiteOriginalEval_measurable [MeasurableSpace (Finset E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) {R : Finset E}
    (T : FiniteRevealTree E R) (H : Finset E) :
    Measurable (fun U : ℕ → ℝ => finiteOriginalEval w U T H) := by
  induction T generalizing H with
  | done => exact measurable_const
  | @query R e he next ih =>
    exact measurable_finite_selection
      (fun b U => finiteOriginalEval w U (next b) (finiteRevealPattern H e b))
      (fun b => ih b _) _
      ((finiteUniformBit_measurable _).comp (measurable_pi_apply R.card))

/-- All cutoffs are measurable functions on the same pair of seed streams. -/
theorem finiteJointHybridEval_measurable [MeasurableSpace (Finset E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (cutoff : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool) :
    Measurable (fun UV : (ℕ → ℝ) × (ℕ → ℝ) =>
      finiteJointHybridEval w f cutoff UV.1 UV.2 T HX HY stopped) := by
  induction T generalizing HX HY stopped with
  | done => exact measurable_const
  | @query R e he next ih =>
    let halted := stopped || decide (finiteDetermines f R HX)
    let bx := fun UV : (ℕ → ℝ) × (ℕ → ℝ) =>
      finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) (UV.1 R.card)
    let z := fun UV : (ℕ → ℝ) × (ℕ → ℝ) =>
      if cutoff ≤ R.card ∧ halted = false then UV.1 R.card else UV.2 R.card
    let byy := fun UV =>
      finiteUniformBit (finitePinnedMean w R HY (fun A => if e ∈ A then 1 else 0)) (z UV)
    have hbx : Measurable bx :=
      (finiteUniformBit_measurable _).comp ((measurable_pi_apply R.card).comp measurable_fst)
    have hz : Measurable z := by
      dsimp [z]
      split_ifs
      · exact (measurable_pi_apply R.card).comp measurable_fst
      · exact (measurable_pi_apply R.card).comp measurable_snd
    have hby : Measurable byy := (finiteUniformBit_measurable _).comp hz
    exact measurable_finite_selection
      (fun b UV => finiteJointHybridEval w f cutoff UV.1 UV.2 (next b.1)
        (finiteRevealPattern HX e b.1) (finiteRevealPattern HY e b.2) halted)
      (fun b => ih b.1 _ _ _) (fun UV => (bx UV, byy UV)) (hbx.prodMk hby)

/-- Threshold notation agrees with the earlier literal update map. -/
theorem finiteRevealPattern_uniformBit (w : Finset E → Set.Ioi (0 : ℝ))
    (R H : Finset E) (e : E) (u : ℝ) :
    finiteRevealPattern H e
        (finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0)) u) =
      finiteThresholdStep w R H e u := by
  by_cases h : 1 - finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0) ≤ u
  · simp [finiteUniformBit, finiteRevealPattern, finiteThresholdStep, h]
  · simp [finiteUniformBit, finiteRevealPattern, finiteThresholdStep, h]

/-- For fixed original U, each actual hybrid is increasing in V and in its
initial hybrid pattern. The original state, original branches and stopping
flag are identical in both recursions. -/
theorem finiteJointHybridEval_monotone (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (cutoff : ℕ) (U : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E)
    {HY HZ : Finset E} (hYZ : HY ⊆ HZ) (stopped : Bool)
    {V W : ℕ → ℝ} (hVW : V ≤ W) :
    finiteJointHybridEval w f cutoff U V T HX HY stopped ⊆
      finiteJointHybridEval w f cutoff U W T HX HZ stopped := by
  induction T generalizing HX HY HZ stopped with
  | done => exact hYZ
  | @query R e he next ih =>
    simp only [finiteJointHybridEval]
    apply ih
    simp only [finiteRevealPattern_uniformBit]
    apply finiteThresholdStep_monotone w hw R hYZ
    split_ifs
    · exact le_rfl
    · exact hVW R.card

end
end PottsContinuity.BD12
