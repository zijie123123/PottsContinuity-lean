module

public import PottsContinuity.BD12.ActiveOriginalQuery

/-! Actual reveal trees query only fresh edges, hence each edge at most once. -/

@[expose] public section

namespace PottsContinuity.BD12
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Any future original query lies outside the already revealed edge set. -/
theorem finiteOriginalQueryAt_not_mem
    (w : Finset E → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) (t : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) (e : E)
    (h : finiteOriginalQueryAt w U t T HX = some e) : e ∉ R := by
  induction T generalizing HX with
  | done => simp only [finiteOriginalQueryAt] at h; cases h
  | @query R a ha next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteOriginalQueryAt, ite_eq_left hlt] at h; cases h
    by_cases heq : t = R.card
    · simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_left heq] at h
      exact (Option.some.inj h) ▸ ha
    simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right heq] at h
    have hchild := ih _ _ h
    exact fun heR => hchild (Finset.mem_insert_of_mem heR)

/-- A fixed original exploration cannot query one edge at distinct times. -/
theorem finiteOriginalQueryAt_time_unique
    (w : Finset E → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) (t s : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) (e : E)
    (ht : finiteOriginalQueryAt w U t T HX = some e)
    (hs : finiteOriginalQueryAt w U s T HX = some e) : t = s := by
  induction T generalizing HX with
  | done => simp only [finiteOriginalQueryAt] at ht; cases ht
  | @query R a ha next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteOriginalQueryAt, ite_eq_left hlt] at ht; cases ht
    by_cases hls : s < R.card
    · simp only [finiteOriginalQueryAt, ite_eq_left hls] at hs; cases hs
    by_cases hteq : t = R.card
    · simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_left hteq] at ht
      have hae : a = e := Option.some.inj ht
      by_cases hseq : s = R.card
      · exact hteq.trans hseq.symm
      simp only [finiteOriginalQueryAt, ite_eq_right hls, ite_eq_right hseq] at hs
      have hnot := finiteOriginalQueryAt_not_mem w U s _ _ e hs
      exact False.elim (hnot (hae ▸ Finset.mem_insert_self a R))
    by_cases hseq : s = R.card
    · simp only [finiteOriginalQueryAt, ite_eq_right hls, ite_eq_left hseq] at hs
      have hae : a = e := Option.some.inj hs
      simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right hteq] at ht
      have hnot := finiteOriginalQueryAt_not_mem w U t _ _ e ht
      exact False.elim (hnot (hae ▸ Finset.mem_insert_self a R))
    simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right hteq] at ht
    simp only [finiteOriginalQueryAt, ite_eq_right hls, ite_eq_right hseq] at hs
    exact ih _ _ ht hs

/-- The stopped active exploration also queries each edge at most once. -/
theorem finiteActiveOriginalQueryAt_time_unique
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ) (U : ℕ → ℝ) (t s : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) (e : E)
    (ht : finiteActiveOriginalQueryAt w f U t T HX = some e)
    (hs : finiteActiveOriginalQueryAt w f U s T HX = some e) : t = s :=
  finiteOriginalQueryAt_time_unique w U t s T HX e
    (finiteActiveOriginalQueryAt_eq_original w f U t T HX e ht)
    (finiteActiveOriginalQueryAt_eq_original w f U s T HX e hs)

end
end PottsContinuity.BD12
