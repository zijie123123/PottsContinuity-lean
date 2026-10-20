module

public import PottsContinuity.BD12.AdaptiveHybridQuery

/-! The original adaptive query made strictly before the observable has been
determined. The exploration stops at the first determining revealed pattern. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Actual active query at zero-based time t. A determining pattern halts the
exploration; no edge is reported after that time or outside the remaining tree. -/
def finiteActiveOriginalQueryAt (w : Finset E → Set.Ioi (0 : ℝ))
    (f : Finset E → ℝ) (U : ℕ → ℝ) (t : ℕ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Option E
  | _, .done, _ => none
  | R, .query e _ next, HX =>
      if t < R.card then none else if finiteDetermines f R HX then none else
        if t = R.card then some e else
          let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) (U R.card)
          finiteActiveOriginalQueryAt w f U t (next bx) (finiteRevealPattern HX e bx)

/-- The active query, including whether stopping has occurred, depends only on
the strict original prefix before t. -/
theorem finiteActiveOriginalQueryAt_congr_prefix
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U U' : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i < t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) :
    finiteActiveOriginalQueryAt w f U t T HX = finiteActiveOriginalQueryAt w f U' t T HX := by
  induction T generalizing HX with
  | done => rfl
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteActiveOriginalQueryAt, ite_eq_left hlt]
    by_cases hd : finiteDetermines f R HX
    · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_left hd]
    by_cases heq : t = R.card
    · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_left heq]
    have hRc : R.card < t := by omega
    simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_right heq, hU _ hRc]
    exact ih _ _

/-- Every active query is the edge in the same original exploration. -/
theorem finiteActiveOriginalQueryAt_eq_original
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U : ℕ → ℝ) (t : ℕ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (e : E) (h : finiteActiveOriginalQueryAt w f U t T HX = some e) :
    finiteOriginalQueryAt w U t T HX = some e := by
  induction T generalizing HX with
  | done => simp only [finiteActiveOriginalQueryAt] at h; cases h
  | @query R a ha next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteActiveOriginalQueryAt, ite_eq_left hlt] at h; cases h
    by_cases hd : finiteDetermines f R HX
    · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_left hd] at h; cases h
    by_cases heq : t = R.card
    · simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_left heq] at h
      simpa only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_left heq] using h
    simp only [finiteActiveOriginalQueryAt, ite_eq_right hlt, ite_eq_right hd, ite_eq_right heq] at h
    simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right heq]
    exact ih _ _ h

end
end PottsContinuity.BD12
