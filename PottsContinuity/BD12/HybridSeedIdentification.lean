module

public import PottsContinuity.BD12.HybridFamilyEvaluation
public import PottsContinuity.BD12.FiniteSeedWindow

/-! Identification of the common-stream deterministic DRT construction with
its shared original-coordinate kernel. This is a joint pushforward identity,
not an assumed conditional-distribution statement. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {E ι : Type*} [Fintype E] [DecidableEq E] [Fintype ι]
    [MeasurableSpace (Finset E)]

omit [Fintype ι] in
/-- The actual joint law of X and all hybrids under finitely many independent
original/replacement inputs is exactly the constructed coupling kernel. -/
theorem finiteHybridFamilyEval_map_seedWindow
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ)
    (background : ℕ → ℝ × ℝ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (HY : ι → Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) :
    (finiteHybridSeedWindow fixedThrough fixedU background R.card n).map
        (finiteHybridFamilyEval w f cutoff T HX HY stopped) =
      finiteHybridFamilyKernel w f fixedThrough fixedU cutoff T HX HY stopped := by
  induction T generalizing HX HY stopped n with
  | done =>
    have hzero : n = 0 := by simpa using hn
    subst n
    rw [finiteHybridSeedWindow, Measure.map_dirac'
      (finiteHybridFamilyEval_measurable w f cutoff .done HX HY stopped)]
    rfl
  | @query R e he next ih =>
    have hcard : R.card + 1 ≤ Fintype.card E := by
      simpa only [Finset.card_insert_of_notMem he] using Finset.card_le_univ (insert e R)
    cases n with
    | zero => omega
    | succ n =>
      have hn' : (insert e R).card + n = Fintype.card E := by
        rw [Finset.card_insert_of_notMem he]
        omega
      let F := finiteHybridFamilyEval w f cutoff (.query e he next) HX HY stopped
      have hF : Measurable F := finiteHybridFamilyEval_measurable w f cutoff _ HX HY stopped
      rw [finiteHybridSeedWindow, Measure.map_map hF (measurable_stream_update R.card),
        finiteKernel_prod_map _ _ _ (hF.comp (measurable_stream_update R.card))]
      rw [finiteHybridFamilyKernel]
      congr 1
      funext uv
      let halted := stopped || decide (finiteDetermines f R HX)
      let bx := finiteUniformBit
        (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) uv.1
      let byy := fun j => finiteUniformBit
        (finitePinnedMean w R (HY j) (fun A => if e ∈ A then 1 else 0))
        (if cutoff j ≤ R.card ∧ halted = false then uv.1 else uv.2)
      have hp : (fun S => F (Function.update S R.card uv)) =
          finiteHybridFamilyEval w f cutoff (next bx) (finiteRevealPattern HX e bx)
            (fun j => finiteRevealPattern (HY j) e (byy j)) halted := by
        funext S
        dsimp only [F]
        rw [finiteHybridFamilyEval_query]
        simp only [Function.update_self]
        exact finiteHybridFamilyEval_update_past w f cutoff (next bx) _ _ halted S R.card
          (by rw [Finset.card_insert_of_notMem he]; omega) uv
      change (finiteHybridSeedWindow fixedThrough fixedU background (R.card + 1) n).map
        (fun S => F (Function.update S R.card uv)) = _
      rw [hp, ← Finset.card_insert_of_notMem he]
      exact ih bx _ _ _ n hn'

/-- A genuine common-space hybrid has the original pinned law even when the
original inputs through its cutoff are fixed. This discharges the earlier
identification gap for the explicit finite independent-input construction. -/
theorem finiteJointHybridEval_map_seedWindow
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough : ℕ) (fixedU : ℕ → ℝ) (cutoff : ι → ℕ)
    (background : ℕ → ℝ × ℝ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (HY : ι → Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) (j : ι) (hj : fixedThrough ≤ cutoff j) :
    (finiteHybridSeedWindow fixedThrough fixedU background R.card n).map
        (fun S => finiteJointHybridEval w f (cutoff j)
          (fun i => (S i).1) (fun i => (S i).2) T HX (HY j) stopped) =
      (finitePinnedLaw w R (HY j)).toMeasure := by
  have h := finiteHybridFamilyKernel_marginal w f fixedThrough fixedU cutoff T HX HY stopped j hj
  rw [← finiteHybridFamilyEval_map_seedWindow w f fixedThrough fixedU cutoff background T
    HX HY stopped n hn, Measure.map_map (g := fun XY : Finset E × (ι → Finset E) => XY.2 j)
      ((measurable_pi_apply j).comp measurable_snd)
      (finiteHybridFamilyEval_measurable w f cutoff T HX HY stopped)] at h
  exact h

end
end PottsContinuity.BD12
