module

public import PottsContinuity.BD12.ActiveOriginalQuery
public import PottsContinuity.BD12.JointHybridSwitch

/-! Adjacent actual hybrids agree off the active original-query event. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- If the active exploration makes no query at t, changing the hybrid cutoff
from t to t+1 changes no final configuration. This includes stopping before t. -/
theorem finiteJointHybridEval_eq_of_no_active_query
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U V : ℕ → ℝ) (t : ℕ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX HY : Finset E) (stopped : Bool)
    (h : finiteActiveOriginalQueryAt w f U t T HX = none) :
    finiteJointHybridEval w f (t + 1) U V T HX HY stopped =
      finiteJointHybridEval w f t U V T HX HY stopped := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    cases stopped with
    | true => exact finiteJointHybridEval_stopped w f (t + 1) t U V _ HX HY
    | false =>
      by_cases hlt : t < R.card
      · exact finiteJointHybridEval_cutoffs_in_past w f (t + 1) t U V _ HX HY false (by omega) (by omega)
      by_cases hd : finiteDetermines f R HX
      · simp only [finiteJointHybridEval, decide_eq_true hd, Bool.false_or,
          Bool.true_eq_false, and_false, ite_false]
        exact finiteJointHybridEval_stopped w f (t + 1) t U V _ _ _
      by_cases heq : t = R.card
      · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_left heq] at h
        cases h
      have hcut : ¬t ≤ R.card := by omega
      have hcut' : ¬t + 1 ≤ R.card := by omega
      simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_right heq] at h
      simp only [finiteJointHybridEval, hcut, hcut', false_and, ite_false]
      exact ih _ _ _ _ h

end
end PottsContinuity.BD12
