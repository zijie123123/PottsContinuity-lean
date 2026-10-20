module

public import PottsContinuity.BD12.HybridFamilyKernel

/-! Deterministic evaluation retaining X and a finite family of hybrids, and
its dependence only on not-yet-used seed coordinates. This locality is needed
to identify the independent-input kernel with an actual common seed space. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {E ι : Type*} [Fintype E] [DecidableEq E]

/-- The original sample only reads times at least the current revealed count. -/
theorem finiteOriginalEval_congr_future (w : Finset E → Set.Ioi (0 : ℝ))
    {R : Finset E} (T : FiniteRevealTree E R) (H : Finset E)
    (U U' : ℕ → ℝ) (hU : ∀ i, R.card ≤ i → U i = U' i) :
    finiteOriginalEval w U T H = finiteOriginalEval w U' T H := by
  induction T generalizing H with
  | done => rfl
  | @query R e he next ih =>
    simp only [finiteOriginalEval, hU R.card le_rfl]
    apply ih
    intro i hi
    exact hU i ((Finset.card_mono (Finset.subset_insert e R)).trans hi)

/-- Earlier seed values have no effect once the current states are specified. -/
theorem finiteJointHybridEval_congr_future (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (cutoff : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (U U' V V' : ℕ → ℝ)
    (hU : ∀ i, R.card ≤ i → U i = U' i) (hV : ∀ i, R.card ≤ i → V i = V' i) :
    finiteJointHybridEval w f cutoff U V T HX HY stopped =
      finiteJointHybridEval w f cutoff U' V' T HX HY stopped := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    simp only [finiteJointHybridEval, hU R.card le_rfl, hV R.card le_rfl]
    apply ih
    · intro i hi
      exact hU i ((Finset.card_mono (Finset.subset_insert e R)).trans hi)
    · intro i hi
      exact hV i ((Finset.card_mono (Finset.subset_insert e R)).trans hi)

/-- All outputs on the common pair-valued seed stream. -/
def finiteHybridFamilyEval (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (cutoff : ι → ℕ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (HY : ι → Finset E) (stopped : Bool)
    (S : ℕ → ℝ × ℝ) : Finset E × (ι → Finset E) :=
  (finiteOriginalEval w (fun i => (S i).1) T HX,
    fun j => finiteJointHybridEval w f (cutoff j)
      (fun i => (S i).1) (fun i => (S i).2) T HX (HY j) stopped)

theorem finiteHybridFamilyEval_measurable [MeasurableSpace (Finset E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (cutoff : ι → ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E)
    (HY : ι → Finset E) (stopped : Bool) :
    Measurable (finiteHybridFamilyEval w f cutoff T HX HY stopped) := by
  have hU : Measurable (fun S : ℕ → ℝ × ℝ => fun i => (S i).1) := by fun_prop
  have hV : Measurable (fun S : ℕ → ℝ × ℝ => fun i => (S i).2) := by fun_prop
  exact ((finiteOriginalEval_measurable w T HX).comp hU).prodMk
    (measurable_pi_iff.mpr (fun j =>
      (finiteJointHybridEval_measurable w f (cutoff j) T HX (HY j) stopped).comp (hU.prodMk hV)))

/-- Updating a seed at the immediately preceding time cannot affect the child
subtree, for either the original sample or any of its hybrids. -/
theorem finiteHybridFamilyEval_update_past (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (cutoff : ι → ℕ) {R : Finset E}
    (T : FiniteRevealTree E R) (HX : Finset E) (HY : ι → Finset E) (stopped : Bool)
    (S : ℕ → ℝ × ℝ) (i : ℕ) (hi : i < R.card) (uv : ℝ × ℝ) :
    finiteHybridFamilyEval w f cutoff T HX HY stopped (Function.update S i uv) =
      finiteHybridFamilyEval w f cutoff T HX HY stopped S := by
  apply Prod.ext
  · apply finiteOriginalEval_congr_future
    intro k hk
    simp only [Function.update_of_ne (show k ≠ i by omega)]
  · funext j
    apply finiteJointHybridEval_congr_future
    · intro k hk
      simp only [Function.update_of_ne (show k ≠ i by omega)]
    · intro k hk
      simp only [Function.update_of_ne (show k ≠ i by omega)]

/-- At a query, the whole family follows the same original bit and the same
halting flag, while each hybrid keeps its own conditional pattern. -/
theorem finiteHybridFamilyEval_query (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (cutoff : ι → ℕ) (R : Finset E)
    (e : E) (he : e ∉ R) (next : Bool → FiniteRevealTree E (insert e R))
    (HX : Finset E) (HY : ι → Finset E) (stopped : Bool) (S : ℕ → ℝ × ℝ) :
    finiteHybridFamilyEval w f cutoff (.query e he next) HX HY stopped S =
      let halted := stopped || decide (finiteDetermines f R HX)
      let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0))
        (S R.card).1
      let byy := fun j => finiteUniformBit
        (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0))
        (if cutoff j ≤ R.card ∧ halted = false then (S R.card).1 else (S R.card).2)
      finiteHybridFamilyEval w f cutoff (next bx) (finiteRevealPattern HX e bx)
        (fun j => finiteRevealPattern (HY j) e (byy j)) halted S := rfl

end
end PottsContinuity.BD12
