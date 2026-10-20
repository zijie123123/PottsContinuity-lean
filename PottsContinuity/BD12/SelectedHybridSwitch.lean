module

public import PottsContinuity.BD12.AdaptiveHybridQuery

/-! The four-term adjacent-hybrid identity at an arbitrary adaptive query time.
Before that time the two hybrids use the same replacement inputs, so the local
query identity propagates through the actual common original exploration. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- DRT's switch identity for FINAL hybrids at the edge actually selected at time t, without
assuming that the initial state already starts at that query. -/
theorem finiteSelectedHybrids_switch_identity
    (w : Finset E → Set.Ioi (0 : ℝ))
    (hw : ∀ A B, (w A : ℝ) * w B ≤ (w (A ∩ B) : ℝ) * w (A ∪ B))
    (f g : Finset E → ℝ) (hg : Monotone g) (U V : ℕ → ℝ) (t : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e) :
    let A := finiteJointHybridEval w f (t + 1) U V T HX HY stopped
    let B := finiteJointHybridEval w f t U V T HX HY stopped
    |g A - g B| = g A * (if e ∈ A then 1 else 0) + g B * (if e ∈ B then 1 else 0) -
      g A * (if e ∈ B then 1 else 0) - g B * (if e ∈ A then 1 else 0) := by
  induction T generalizing HX HY stopped with
  | done => simp only [finiteOriginalQueryAt] at hquery; cases hquery
  | @query R a ha next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteOriginalQueryAt, ite_eq_left hlt] at hquery
      cases hquery
    by_cases heq : t = R.card
    · have hae : a = e := Option.some.inj (by
        simpa only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_left heq] using hquery)
      subst e
      subst t
      exact finiteJointHybrids_adjacent_query_identity w hw f g hg U V R HX HY a ha next stopped
    have hcut : ¬t ≤ R.card := by omega
    have hcut' : ¬t + 1 ≤ R.card := by omega
    simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right heq] at hquery
    simp only [finiteJointHybridEval, hcut, hcut', false_and, ite_false]
    exact ih _ _ _ _ hquery

end
end PottsContinuity.BD12
