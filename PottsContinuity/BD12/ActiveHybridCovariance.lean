module

public import PottsContinuity.BD12.ActiveHybridStopping
public import PottsContinuity.BD12.SelectedHybridCovariance
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The covariance estimate with the actual stopping-aware selected edge.
The no-query branch has zero cost by the proved stopped hybrid equality. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Conditional cost before prefix averaging: it vanishes off the actual active
query event, and is bounded by twice the covariance at its selected edge on it. -/
theorem finiteActiveHybrid_switch_cost_le
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f : Finset E → ℝ) (hf : Monotone f) (hf01 : ∀ A, f A ∈ Set.Icc (0 : ℝ) 1)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅) :
    (∫ W, ∫ v,
      |f (finiteJointHybridEval w f (t + 1) W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) -
        f (finiteJointHybridEval w f t W (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)|
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
      ∂finiteOriginalPinBlock t (Fintype.card E - t) U) ≤
      match finiteActiveOriginalQueryAt w f U t T ∅ with
      | none => 0
      | some e => 2 * (finitePinnedMean w ∅ ∅ (fun A => f A * (if e ∈ A then 1 else 0)) -
          finitePinnedMean w ∅ ∅ f * finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0)) := by
  cases hquery : finiteActiveOriginalQueryAt w f U t T ∅ with
  | some e =>
    exact finiteSelectedHybrid_switch_cost_le_twice_covariance w hw f hf hf01 U V t T e
      (finiteActiveOriginalQueryAt_eq_original w f U t T ∅ e hquery)
  | none =>
    apply le_of_eq
    calc
      _ = ∫ _W : ℕ → ℝ, (0 : ℝ) ∂finiteOriginalPinBlock t (Fintype.card E - t) U := by
        apply integral_congr_ae
        filter_upwards [finiteOriginalPinBlock_ae_past t (Fintype.card E - t) U] with W hW
        have hqueryW : finiteActiveOriginalQueryAt w f W t T ∅ = none :=
          (finiteActiveOriginalQueryAt_congr_prefix w f U W t
            (fun i hi => (hW i hi).symm) T ∅).symm.trans hquery
        have heq (v : Fin (Fintype.card E) → ℝ) :=
          finiteJointHybridEval_eq_of_no_active_query w f W
            (finiteSeedExtension (Fintype.card E) V v) t T ∅ ∅ false hqueryW
        simp_rw [heq, sub_self, abs_zero]
        simp only [integral_zero]
      _ = 0 := integral_zero _ _

end
end PottsContinuity.BD12
