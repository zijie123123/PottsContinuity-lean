module

public import PottsContinuity.BD12.HybridFiberSampler
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! DRT's original sample and all stopped hybrids on one common pair of seed
streams. These are actual deterministic maps, before any probabilistic law is
attached. Time is zero-based, and equals the number of revealed coordinates. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The original adaptive sample driven by U. -/
def finiteOriginalEval (w : Finset E → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Finset E
  | _, .done, H => H
  | R, .query e _ next, H =>
      let b := finiteUniformBit (finitePinnedMean w R H (fun A => if e ∈ A then 1 else 0))
        (U R.card)
      finiteOriginalEval w U (next b) (finiteRevealPattern H e b)

/-- The hybrid on the SAME (U,V) space for every cutoff. Its reveal order is
chosen using the original X, while its own conditional bits use V before the
cutoff and after determination, and U between those times. -/
def finiteJointHybridEval (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (cutoff : ℕ) (U V : ℕ → ℝ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Finset E → Bool → Finset E
  | _, .done, _, HY, _ => HY
  | R, .query e _ next, HX, HY, stopped =>
      let halted := stopped || decide (finiteDetermines f R HX)
      let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0))
        (U R.card)
      let z := if cutoff ≤ R.card ∧ halted = false then U R.card else V R.card
      let byy := finiteUniformBit (finitePinnedMean w R HY (fun A => if e ∈ A then 1 else 0)) z
      finiteJointHybridEval w f cutoff U V (next bx)
        (finiteRevealPattern HX e bx) (finiteRevealPattern HY e byy) halted

omit [Fintype E] in
/-- Updating a fresh coordinate preserves the entire earlier pattern. -/
theorem finiteRevealPattern_inter (R H : Finset E) (e : E) (he : e ∉ R) (b : Bool) :
    finiteRevealPattern H e b ∩ R = H ∩ R := by
  ext a
  cases b <;> by_cases ha : a = e <;> simp [finiteRevealPattern, ha, he]

/-- Original sampling never changes already revealed coordinates. -/
theorem finiteOriginalEval_inter (w : Finset E → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (H : Finset E) :
    finiteOriginalEval w U T H ∩ R = H ∩ R := by
  induction T generalizing H with
  | done => rfl
  | @query R e he next ih =>
    simp only [finiteOriginalEval]
    generalize finiteUniformBit _ _ = b
    have h := congrArg (fun A : Finset E => A ∩ R) (ih b (finiteRevealPattern H e b))
    simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.subset_insert e R),
      finiteRevealPattern_inter R H e he b] using h

/-- The hybrid also preserves its already revealed coordinates, although its
future order is chosen by the original sample. -/
theorem finiteJointHybridEval_inter (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (cutoff : ℕ) (U V : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool) :
    finiteJointHybridEval w f cutoff U V T HX HY stopped ∩ R = HY ∩ R := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    simp only [finiteJointHybridEval]
    generalize finiteUniformBit _ (U R.card) = bx
    generalize finiteUniformBit _ _ = byy
    have h := congrArg (fun A : Finset E => A ∩ R)
      (ih bx (finiteRevealPattern HX e bx) (finiteRevealPattern HY e byy)
        (stopped || decide (finiteDetermines f R HX)))
    simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr (Finset.subset_insert e R),
      finiteRevealPattern_inter R HY e he byy] using h

/-- Once stopped, the hybrid is independent of the cutoff, pointwise in both
seed streams. This supplies the source's vanishing increments after stopping. -/
theorem finiteJointHybridEval_stopped (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (s t : ℕ) (U V : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) :
    finiteJointHybridEval w f s U V T HX HY true =
      finiteJointHybridEval w f t U V T HX HY true := by
  induction T generalizing HX HY with
  | done => rfl
  | @query R e he next ih =>
    simpa only [finiteJointHybridEval, Bool.true_or, Bool.true_eq_false, and_false,
      ite_false] using ih _ _ _

/-- The zero-cutoff hybrid agrees with the original observable. All subsequent
coordinates after determination may change, as in DRT's actual construction. -/
theorem finiteJointHybridEval_zero_observable (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (U V : ℕ → ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (H : Finset E) :
    f (finiteJointHybridEval w f 0 U V T H H false) = f (finiteOriginalEval w U T H) := by
  induction T generalizing H with
  | done => rfl
  | @query R e he next ih =>
    by_cases hd : finiteDetermines f R H
    · exact (hd _ (finiteJointHybridEval_inter w f 0 U V (.query e he next) H H false)).trans
        (hd _ (finiteOriginalEval_inter w U (.query e he next) H)).symm
    · simpa only [finiteJointHybridEval, finiteOriginalEval, Bool.false_or,
        decide_eq_false hd, Nat.zero_le, and_true, ite_true] using ih _ _

end
end PottsContinuity.BD12
