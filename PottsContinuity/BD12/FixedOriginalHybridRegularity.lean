module

public import PottsContinuity.BD12.FixedOriginalHybridMoments
public import PottsContinuity.BD12.SelectedHybridBitPrefix
public import PottsContinuity.BD12.BoundedVarianceDistance
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! Measurability of fixed-U hybrid moments and the exact mean of the replaced
selected bit. The latter is derived from the actual block tower and the proved
short-prefix dependence. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Every actual selected query time is strictly below the total edge count. -/
theorem finiteOriginalQueryAt_lt_card (w : Finset E → Set.Ioi (0 : ℝ))
    (U : ℕ → ℝ) (t : ℕ) {R : Finset E} (T : FiniteRevealTree E R)
    (HX : Finset E) (e : E) (hquery : finiteOriginalQueryAt w U t T HX = some e) :
    t < Fintype.card E := by
  induction T generalizing HX with
  | done => simp only [finiteOriginalQueryAt] at hquery; cases hquery
  | @query R a ha next ih =>
    by_cases hlt : t < R.card
    · simp only [finiteOriginalQueryAt, ite_eq_left hlt] at hquery
      cases hquery
    by_cases heq : t = R.card
    · have hcard := Finset.card_le_univ (insert a R)
      rw [Finset.card_insert_of_notMem ha] at hcard
      omega
    simp only [finiteOriginalQueryAt, ite_eq_right hlt, ite_eq_right heq] at hquery
    exact ih _ _ hquery

variable [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- The actual finite-V-product moment is measurable as a function of U. -/
theorem finiteJointHybridEval_product_integral_measurable
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (cutoff : ℕ) (V : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    Measurable (fun U : ℕ → ℝ => ∫ v,
      g (finiteJointHybridEval w f cutoff U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) := by
  have hinput : Measurable (fun p : (ℕ → ℝ) × (Fin (Fintype.card E) → ℝ) =>
      (p.1, finiteSeedExtension (Fintype.card E) V p.2)) :=
    measurable_fst.prodMk ((finiteSeedExtension_measurable _ V).comp measurable_snd)
  have h : Measurable (fun p : (ℕ → ℝ) × (Fin (Fintype.card E) → ℝ) =>
      g (finiteJointHybridEval w f cutoff p.1
        (finiteSeedExtension (Fintype.card E) V p.2) T ∅ ∅ false)) :=
    (measurable_of_finite g).comp ((finiteJointHybridEval_measurable w f cutoff T ∅ ∅ false).comp hinput)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- Unit-bounded observables have unit-bounded actual fixed-U moments. -/
theorem finiteJointHybridEval_product_integral_mem_Icc
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (cutoff : ℕ) (U V : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    (∫ v, g (finiteJointHybridEval w f cutoff U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : Measurable (fun v : Fin (Fintype.card E) → ℝ =>
      g (finiteJointHybridEval w f cutoff U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)) :=
    (measurable_of_finite g).comp ((finiteJointHybridEval_measurable w f cutoff T ∅ ∅ false).comp
      (measurable_const.prodMk (finiteSeedExtension_measurable _ V)))
  have hi := integrable_of_unit_bounds (Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) hm (fun _ => hg01 _)
  refine ⟨integral_nonneg (fun _ => (hg01 _).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun _ => (hg01 _).2)

/-- Source's replaced selected-bit coefficient is exactly its original-law
mean, pointwise in the entire fixed original stream U. -/
theorem finiteSelectedHybrid_replaced_bit_mean
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (U V : ℕ → ℝ) (t : ℕ) (T : FiniteRevealTree E ∅)
    (e : E) (hquery : finiteOriginalQueryAt w U t T ∅ = some e) :
    (∫ v, (if e ∈ finiteJointHybridEval w f (t + 1) U
      (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) =
      finitePinnedMean w ∅ ∅ (fun A => if e ∈ A then 1 else 0) := by
  let I := fun A : Finset E => if e ∈ A then (1 : ℝ) else 0
  have hI : ∀ A, I A ∈ Set.Icc (0 : ℝ) 1 := by intro A; dsimp [I]; split_ifs <;> norm_num
  have ht := finiteOriginalQueryAt_lt_card w U t T ∅ e hquery
  have havg := finiteJointHybridEval_product_block_integral w f I hI t (t + 1) U V
    (fun i => (U i, V i)) T ht.le (by omega)
  have hfactor := finiteJointHybrid_replaced_bit_block_factor w f U V t
    (Fintype.card E - t) (Fintype.card E) T ∅ ∅ false e hquery (fun _ => 1)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at hfactor
  exact hfactor.symm.trans havg

end
end PottsContinuity.BD12
