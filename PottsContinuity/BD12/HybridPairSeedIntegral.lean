module

public import PottsContinuity.BD12.FixedOriginalHybridMoments
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Transfer joint hybrid observables between the two independent input fields
and the common paired seed law used by the variance telescoping argument. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Joint moments of two cutoffs under the actual fixed-U replacement product
are their moments under the fully fixed-original paired seed window. -/
theorem finiteHybridPair_product_integral_eq_seedWindow
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (g : Finset E × Finset E → ℝ) (s t : ℕ) (U V : ℕ → ℝ)
    (background : ℕ → ℝ × ℝ) (T : FiniteRevealTree E ∅) :
    (∫ v, g (finiteJointHybridEval w f s U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false,
      finiteJointHybridEval w f t U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) =
    ∫ S, g (finiteJointHybridEval w f s (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false,
      finiteJointHybridEval w f t (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false)
      ∂finiteHybridSeedWindow (Fintype.card E) U background 0 (Fintype.card E) := by
  have h := finiteFixedHybridFamily_product_integral w f U V
    (fun b : Bool => if b then s else t) background T (fun XY => g (XY.2 true, XY.2 false))
  simpa only [finiteHybridFamilyEval, Bool.false_eq_true, ite_false, ite_true] using h

/-- Averaging the actual independent U/V products gives the common seed law,
for arbitrary unit-bounded joint observables of two final hybrids. -/
theorem finiteHybridPair_product_block_integral_eq_seedWindow
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (g : Finset E × Finset E → ℝ) (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (s t : ℕ) (U V : ℕ → ℝ) (background : ℕ → ℝ × ℝ) (T : FiniteRevealTree E ∅) :
    (∫ W, ∫ v, g (finiteJointHybridEval w f s W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false,
      finiteJointHybridEval w f t W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
      ∂finiteOriginalPinBlock 0 (Fintype.card E) U) =
    ∫ S, g (finiteJointHybridEval w f s (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false,
      finiteJointHybridEval w f t (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false)
      ∂finiteHybridSeedWindow 0 U background 0 (Fintype.card E) := by
  simp_rw [finiteHybridPair_product_integral_eq_seedWindow w f g s t _ V background T]
  let G := fun S : ℕ → ℝ × ℝ =>
    g (finiteJointHybridEval w f s (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false,
      finiteJointHybridEval w f t (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false)
  have hinput : Measurable (fun S : ℕ → ℝ × ℝ => ((fun i => (S i).1), (fun i => (S i).2))) := by fun_prop
  have hY (r : ℕ) : Measurable (fun S : ℕ → ℝ × ℝ =>
      finiteJointHybridEval w f r (fun i => (S i).1) (fun i => (S i).2) T ∅ ∅ false) :=
    (finiteJointHybridEval_measurable w f r T ∅ ∅ false).comp hinput
  have hG : Measurable G := (measurable_of_finite g).comp ((hY s).prodMk (hY t))
  simpa only [Nat.zero_add] using finiteOriginalPinBlock_seed_integral 0 (Fintype.card E) U background 0 (Fintype.card E)
    G hG (fun _ => hg01 _)

end
end PottsContinuity.BD12
