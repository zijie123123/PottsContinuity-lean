module

public import PottsContinuity.BD12.ActiveOriginalQuery
public import PottsContinuity.BD12.JointHybridRegularity

/-! Measurability of the actual stopping-aware adaptive query. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The active query is measurable in the original seed stream, even before a
specific measurable structure on its finite output carrier is chosen. -/
theorem finiteActiveOriginalQueryAt_measurable [MeasurableSpace (Option E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (t : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) :
    Measurable (fun U : ℕ → ℝ => finiteActiveOriginalQueryAt w f U t T HX) := by
  induction T generalizing HX with
  | done => exact measurable_const
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simpa only [finiteActiveOriginalQueryAt, ite_eq_left hlt] using
        (measurable_const : Measurable (fun _ : ℕ → ℝ => (none : Option E)))
    by_cases hd : finiteDetermines f R HX
    · simpa only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_left hd] using
        (measurable_const : Measurable (fun _ : ℕ → ℝ => (none : Option E)))
    by_cases heq : t = R.card
    · simpa only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_left heq] using
        (measurable_const : Measurable (fun _ : ℕ → ℝ => (some e : Option E)))
    let b := fun U : ℕ → ℝ =>
      finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) (U R.card)
    have hb : Measurable b := (finiteUniformBit_measurable _).comp (measurable_pi_apply R.card)
    simpa only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_right heq] using
      measurable_finite_selection
        (fun a U => finiteActiveOriginalQueryAt w f U t (next a) (finiteRevealPattern HX e a))
        (fun a => ih a _) b hb

/-- In particular, every active selected-edge fibre is a measurable event. -/
theorem finiteActiveOriginalQueryAt_fibre_measurableSet
    [MeasurableSpace (Option E)] [MeasurableSingletonClass (Option E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (t : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) (e : E) :
    MeasurableSet {U : ℕ → ℝ | finiteActiveOriginalQueryAt w f U t T HX = some e} :=
  (measurableSet_singleton (some e)).preimage (finiteActiveOriginalQueryAt_measurable w f t T HX)

end
end PottsContinuity.BD12
