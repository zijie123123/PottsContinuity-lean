module

public import PottsContinuity.BD12.JointHybridRegularity
public import PottsContinuity.BD12.HarrisFiniteProduct

/-! Harris association for the actual common-space hybrids, with original U
fixed. Fresh replacement coordinates are a finite independent uniform vector;
the unsampled stream coordinates keep a specified background. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section

/-- Replace the first n coordinates of a prescribed stream by the finite seed
vector. Outside that window retain the prescribed stream on its whole carrier. -/
def finiteSeedExtension (n : ℕ) (background : ℕ → ℝ) (v : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if hi : i < n then v ⟨i, hi⟩ else background i

theorem finiteSeedExtension_measurable (n : ℕ) (background : ℕ → ℝ) :
    Measurable (finiteSeedExtension n background) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i < n
  · simpa only [finiteSeedExtension, dite_eq_left hi] using measurable_pi_apply (⟨i, hi⟩ : Fin n)
  · simpa only [finiteSeedExtension, dite_eq_right hi] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => background i))

theorem finiteSeedExtension_monotone (n : ℕ) (background : ℕ → ℝ) :
    Monotone (finiteSeedExtension n background) := by
  intro v v' hv i
  by_cases hi : i < n
  · simpa only [finiteSeedExtension, dite_eq_left hi] using hv ⟨i, hi⟩
  · simp only [finiteSeedExtension, dite_eq_right hi, le_refl]

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace (Finset E)]

/-- The two actual hybrids, driven by the same replacement vector V with the
original U fixed, obey Harris. Their cutoffs may differ, as required for both
cross terms in DRT's switch estimate. -/
theorem finiteJointHybrids_positive_association
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g h : Finset E → ℝ) (s t n : ℕ) (U background : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY HZ : Finset E) (stopped : Bool)
    (hg : Measurable g) (hh : Measurable h) (hgm : Monotone g) (hhm : Monotone h)
    (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (hh01 : ∀ A, h A ∈ Set.Icc (0 : ℝ) 1) :
    let Y := fun v => finiteJointHybridEval w f s U (finiteSeedExtension n background v) T HX HY stopped
    let Z := fun v => finiteJointHybridEval w f t U (finiteSeedExtension n background v) T HX HZ stopped
    (∫ v, g (Y v) ∂Measure.pi (fun _ : Fin n => finiteUnitUniform)) *
        (∫ v, h (Z v) ∂Measure.pi (fun _ : Fin n => finiteUnitUniform)) ≤
      ∫ v, g (Y v) * h (Z v) ∂Measure.pi (fun _ : Fin n => finiteUnitUniform) := by
  let Y := fun v => finiteJointHybridEval w f s U (finiteSeedExtension n background v) T HX HY stopped
  let Z := fun v => finiteJointHybridEval w f t U (finiteSeedExtension n background v) T HX HZ stopped
  have hinput : Measurable (fun v : Fin n → ℝ => (U, finiteSeedExtension n background v)) :=
    measurable_const.prodMk (finiteSeedExtension_measurable n background)
  have hY : Measurable Y := (finiteJointHybridEval_measurable w f s T HX HY stopped).comp hinput
  have hZ : Measurable Z := (finiteJointHybridEval_measurable w f t T HX HZ stopped).comp hinput
  have hYm : Monotone Y := fun v v' hv =>
    finiteJointHybridEval_monotone w hw f s U T HX le_rfl stopped
      (finiteSeedExtension_monotone n background hv)
  have hZm : Monotone Z := fun v v' hv =>
    finiteJointHybridEval_monotone w hw f t U T HX le_rfl stopped
      (finiteSeedExtension_monotone n background hv)
  exact harris_finite_product finiteUnitUniform n (fun v => g (Y v)) (fun v => h (Z v))
    (hg.comp hY) (hh.comp hZ) (hgm.comp hYm) (hhm.comp hZm)
    (fun v => hg01 _) (fun v => hh01 _)

end
end PottsContinuity.BD12
