module

public import PottsContinuity.BD12.FixedOriginalHybridMoments
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Moments of the actual original adaptive sample under its independent
uniform inputs. The zero-cutoff observable identity removes the auxiliary
replacement inputs from the already proved hybrid moment law. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Actual original-input expectation for every complete adaptive reveal tree.
No sampling or moment identity is required as a premise. -/
theorem finiteOriginalEval_block_integral
    (w : Finset E → Set.Ioi (0 : ℝ)) (g : Finset E → ℝ)
    (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (U : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    (∫ W, g (finiteOriginalEval w W T ∅) ∂finiteOriginalPinBlock 0 (Fintype.card E) U) =
      finitePinnedMean w ∅ ∅ g := by
  have h := finiteJointHybridEval_product_block_integral w g g hg01 0 0 U (fun _ => 0)
    (fun i => (U i, 0)) T (Nat.zero_le _) le_rfl
  simp_rw [finiteJointHybridEval_zero_observable] at h
  simpa only [Nat.sub_zero, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

end
end PottsContinuity.BD12
