module

public import PottsContinuity.BD12.HybridQueryCoordinate

/-! The edge selected at a given adaptive exploration time, and the literal
hybrid bit there. Option.none means that the queried time is outside the
remaining exploration, not a supplied edge or bit. -/

@[expose] public section

namespace PottsContinuity.BD12
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The actual original query at time t, with zero-based time = revealed count. -/
def finiteOriginalQueryAt (w : Finset E → Set.Ioi (0 : ℝ)) (U : ℕ → ℝ) (t : ℕ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Option E
  | _, .done, _ => none
  | R, .query e _ next, HX =>
      if t < R.card then none else if t = R.card then some e else
        let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) (U R.card)
        finiteOriginalQueryAt w U t (next bx) (finiteRevealPattern HX e bx)

/-- The actual hybrid answer at the original-selected query at time t. -/
def finiteHybridQueryAt (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (cutoff : ℕ) (U V : ℕ → ℝ) (t : ℕ) :
    {R : Finset E} → FiniteRevealTree E R → Finset E → Finset E → Bool → Option (E × Bool)
  | _, .done, _, _, _ => none
  | R, .query e _ next, HX, HY, stopped =>
      if t < R.card then none else
        let halted := stopped || decide (finiteDetermines f R HX)
        let bx := finiteUniformBit (finitePinnedMean w R HX (fun A => if e ∈ A then 1 else 0)) (U R.card)
        let byy := finiteUniformBit (finitePinnedMean w R HY (fun A => if e ∈ A then 1 else 0))
          (if cutoff ≤ R.card ∧ halted = false then U R.card else V R.card)
        if t = R.card then some (e, byy) else
          finiteHybridQueryAt w f cutoff U V t (next bx)
            (finiteRevealPattern HX e bx) (finiteRevealPattern HY e byy) halted

/-- The selected edge is determined by the STRICT original prefix. -/
theorem finiteOriginalQueryAt_congr_prefix (w : Finset E → Set.Ioi (0 : ℝ))
    (U U' : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i < t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX : Finset E) :
    finiteOriginalQueryAt w U t T HX = finiteOriginalQueryAt w U' t T HX := by
  induction T generalizing HX with
  | done => rfl
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteOriginalQueryAt, hlt, ite_true]
    by_cases heq : t = R.card
    · simp only [finiteOriginalQueryAt, heq, ite_true]
    simp only [finiteOriginalQueryAt, hlt, ite_false, heq,
      hU R.card (by omega)]
    exact ih _ _

/-- With the current input replaced, the selected edge AND its hybrid answer
are functions of only the strict original prefix and replacement inputs. -/
theorem finiteHybridQueryAt_replaced_congr_prefix
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U U' V : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i < t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool) :
    finiteHybridQueryAt w f (t + 1) U V t T HX HY stopped =
      finiteHybridQueryAt w f (t + 1) U' V t T HX HY stopped := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteHybridQueryAt, hlt, ite_true]
    have hcut : ¬t + 1 ≤ R.card := by omega
    by_cases heq : t = R.card
    · simp only [finiteHybridQueryAt, ite_eq_right hlt, ite_eq_left heq,
        ite_eq_right (show ¬(t + 1 ≤ R.card ∧ (stopped || decide (finiteDetermines f R HX)) = false)
          from fun h => hcut h.1)]
    simp only [finiteHybridQueryAt, hlt, ite_false, heq, hcut, false_and,
      hU R.card (by omega)]
    exact ih _ _ _ _

/-- For the preceding hybrid cutoff, including the current original input in
the prefix suffices; all future original inputs are irrelevant. -/
theorem finiteHybridQueryAt_original_congr_prefix
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U U' V : ℕ → ℝ) (t : ℕ) (hU : ∀ i, i ≤ t → U i = U' i)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool) :
    finiteHybridQueryAt w f t U V t T HX HY stopped =
      finiteHybridQueryAt w f t U' V t T HX HY stopped := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteHybridQueryAt, hlt, ite_true]
    by_cases heq : t = R.card
    · simp only [finiteHybridQueryAt, ite_eq_right hlt, ite_eq_left heq, hU R.card (by omega)]
    simp only [finiteHybridQueryAt, ite_eq_right hlt, ite_eq_right heq, hU R.card (by omega)]
    exact ih _ _ _ _

/-- The bit returned at the adaptive query is the bit of the ACTUAL final
common-space hybrid at that edge, not merely a separately sampled bit. -/
theorem finiteHybridQueryAt_eq_final
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (cutoff : ℕ) (U V : ℕ → ℝ) (t : ℕ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool) :
    finiteHybridQueryAt w f cutoff U V t T HX HY stopped =
      (finiteOriginalQueryAt w U t T HX).map (fun e =>
        (e, decide (e ∈ finiteJointHybridEval w f cutoff U V T HX HY stopped))) := by
  induction T generalizing HX HY stopped with
  | done => rfl
  | @query R e he next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteHybridQueryAt, finiteOriginalQueryAt, ite_eq_left hlt, Option.map_none]
    by_cases heq : t = R.card
    · have hmem := finiteJointHybridEval_query_mem w f cutoff U V R HX HY e he next stopped
      have hb : finiteUniformBit (finitePinnedMean w R HY (fun A => if e ∈ A then 1 else 0))
          (if cutoff ≤ R.card ∧ (stopped || decide (finiteDetermines f R HX)) = false
            then U R.card else V R.card) =
          decide (e ∈ finiteJointHybridEval w f cutoff U V (.query e he next) HX HY stopped) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using hmem.symm
      simp only [finiteHybridQueryAt, finiteOriginalQueryAt, ite_eq_right hlt,
        ite_eq_left heq, Option.map_some, hb]
    simp only [finiteHybridQueryAt, finiteOriginalQueryAt, ite_eq_right hlt,
      ite_eq_right heq, finiteJointHybridEval]
    exact ih _ _ _ _

end
end PottsContinuity.BD12
