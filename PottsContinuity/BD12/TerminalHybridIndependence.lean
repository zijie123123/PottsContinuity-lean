module

public import PottsContinuity.BD12.HybridSeedIdentification
public import PottsContinuity.BD12.IndependentKernelProduct

/-! The all-replacement terminal hybrid is independent of the original output
in the actual common-input coupling, even though its reveal order is chosen
by the original sample. This uses independent conditional bit kernels, not an
independence hypothesis. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Joint law of the original sample and a terminal all-replacement hybrid.
The already specified states may differ; future original inputs must be fresh. -/
theorem finiteHybridFamilyKernel_terminal_product
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E)
    (HY : ι → Finset E) (stopped : Bool) (j : ι)
    (hj : Fintype.card E ≤ cutoff j) (hfresh : fixedThrough ≤ R.card) :
    (finiteHybridFamilyKernel w f fixedThrough fixedU cutoff T HX HY stopped).map
        (fun XY => (XY.1, XY.2 j)) =
      (finitePinnedLaw w R HX).toMeasure.prod (finitePinnedLaw w R (HY j)).toMeasure := by
  induction T generalizing HX HY stopped with
  | done =>
    rw [finiteHybridFamilyKernel, Measure.map_dirac'
      (show Measurable (fun XY : Finset E × (ι → Finset E) => (XY.1, XY.2 j)) by fun_prop)]
    rw [finitePinnedLaw_univ, finitePinnedLaw_univ, PMF.toMeasure_pure, PMF.toMeasure_pure,
      Measure.dirac_prod_dirac]
  | @query R e he next ih =>
    have hcard : R.card + 1 ≤ Fintype.card E := by
      simpa only [Finset.card_insert_of_notMem he] using Finset.card_le_univ (insert e R)
    have hcut : ¬cutoff j ≤ R.card := by omega
    have hprefix : ¬R.card < fixedThrough := Nat.not_lt.mpr hfresh
    rw [finiteHybridFamilyKernel, finiteKernel_map_bind _ _
      (finiteHybridFamilyKernel_node_measurable w f fixedThrough fixedU cutoff R e he next HX HY stopped)
      (fun XY => (XY.1, XY.2 j)) (by fun_prop)]
    have hrec := fun b HX' HY' stopped' =>
      ih b HX' HY' stopped' (hfresh.trans (Finset.card_mono (Finset.subset_insert e R)))
    simp_rw [hrec]
    simp only [hcut, false_and, ite_false, finiteHybridAuxLaw, hprefix]
    let K : ℝ → Measure (Finset E) := fun u =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern HX e
        (finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) u))).toMeasure
    let L : ℝ → Measure (Finset E) := fun v =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e
        (finiteUniformBit (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0)) v))).toMeasure
    have hK : Measurable K := (measurable_of_finite (fun b : Bool =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern HX e b)).toMeasure)).comp
        (finiteUniformBit_measurable _)
    have hL : Measurable L := (measurable_of_finite (fun b : Bool =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e b)).toMeasure)).comp
        (finiteUniformBit_measurable _)
    let px := finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)
    let py := finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0)
    let P : Bool → Measure (Finset E) := fun b =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern HX e b)).toMeasure
    let Q : Bool → Measure (Finset E) := fun b =>
      (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e b)).toMeasure
    let bits : ℝ × ℝ → Bool × Bool := fun uv =>
      (finiteUniformBit px uv.1, finiteUniformBit py uv.2)
    have hbits : Measurable bits :=
      ((finiteUniformBit_measurable px).comp measurable_fst).prodMk
        ((finiteUniformBit_measurable py).comp measurable_snd)
    have hprod : Measurable (fun b : Bool × Bool => (P b.1).prod (Q b.2)) :=
      measurable_of_finite _
    have hKL : Measurable (fun uv : ℝ × ℝ => (K uv.1).prod (L uv.2)) := by
      change Measurable ((fun b : Bool × Bool => (P b.1).prod (Q b.2)) ∘ bits)
      exact hprod.comp hbits
    change (finiteUnitUniform.prod finiteUnitUniform).bind
      (fun uv => (K uv.1).prod (L uv.2)) = _
    rw [finiteKernel_independent_bind _ _ K L hK hL hKL]
    dsimp only [K, L]
    rw [finiteUnitUniform_bind_reveal w R HX e he
      (fun b => (finitePinnedLaw w (insert e R) (finiteRevealPattern HX e b)).toMeasure),
      finiteUnitUniform_bind_reveal w R (HY j) e he
        (fun b => (finitePinnedLaw w (insert e R) (finiteRevealPattern (HY j) e b)).toMeasure),
      finitePMF_toMeasure_bind, finitePMF_toMeasure_bind,
      finitePinnedLaw_bind_reveal, finitePinnedLaw_bind_reveal]

/-- Independence transferred to the actual deterministic common seed maps. -/
theorem finiteHybridFamilyEval_terminal_product
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedU : ℕ → ℝ) (cutoff : ι → ℕ) (background : ℕ → ℝ × ℝ)
    (T : FiniteRevealTree E ∅) (j : ι) (hj : Fintype.card E ≤ cutoff j) :
    (finiteHybridSeedWindow 0 fixedU background 0 (Fintype.card E)).map
        (fun S => (finiteOriginalEval w (fun i => (S i).1) T ∅,
          finiteJointHybridEval w f (cutoff j)
            (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false)) =
      (finitePinnedLaw w ∅ ∅).toMeasure.prod (finitePinnedLaw w ∅ ∅).toMeasure := by
  have h := finiteHybridFamilyKernel_terminal_product w f 0 fixedU cutoff T ∅
    (fun _ => ∅) false j hj (by simp)
  rw [← finiteHybridFamilyEval_map_seedWindow w f 0 fixedU cutoff background T ∅ (fun _ => ∅)
    false (Fintype.card E) (by simp), Measure.map_map
      (g := fun XY : Finset E × (ι → Finset E) => (XY.1, XY.2 j))
      (by fun_prop) (finiteHybridFamilyEval_measurable w f cutoff T ∅ (fun _ => ∅) false)] at h
  simpa only [Finset.card_empty, Function.comp_def, finiteHybridFamilyEval] using h

end
end PottsContinuity.BD12
