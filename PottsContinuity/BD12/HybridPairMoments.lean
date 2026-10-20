module

public import PottsContinuity.BD12.FixedOriginalHybridRegularity
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! Measurability and bounds for actual joint moments of two hybrid cutoffs. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)] [MeasurableSingletonClass (Finset E)]

/-- Any real observable of a pair of finite hybrids has a measurable V-mean. -/
theorem finiteHybridPair_product_integral_measurable
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (g : Finset E × Finset E → ℝ) (s t : ℕ) (V : ℕ → ℝ)
    (T : FiniteRevealTree E ∅) :
    Measurable (fun U : ℕ → ℝ => ∫ v,
      g (finiteJointHybridEval w f s U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false,
        finiteJointHybridEval w f t U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) := by
  have hinput : Measurable (fun z : (ℕ → ℝ) × (Fin (Fintype.card E) → ℝ) =>
      (z.1, finiteSeedExtension (Fintype.card E) V z.2)) :=
    measurable_fst.prodMk ((finiteSeedExtension_measurable _ V).comp measurable_snd)
  have hY (r : ℕ) : Measurable (fun z : (ℕ → ℝ) × (Fin (Fintype.card E) → ℝ) =>
      finiteJointHybridEval w f r z.1 (finiteSeedExtension (Fintype.card E) V z.2) T ∅ ∅ false) :=
    (finiteJointHybridEval_measurable w f r T ∅ ∅ false).comp hinput
  have hg : Measurable g := measurable_of_finite g
  exact (hg.comp ((hY s).prodMk (hY t))).stronglyMeasurable.integral_prod_right'.measurable

/-- Unit-bounded pair observables retain these bounds after V averaging. -/
theorem finiteHybridPair_product_integral_mem_Icc
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (g : Finset E × Finset E → ℝ) (hg01 : ∀ A, g A ∈ Set.Icc (0 : ℝ) 1)
    (s t : ℕ) (U V : ℕ → ℝ) (T : FiniteRevealTree E ∅) :
    (∫ v, g (finiteJointHybridEval w f s U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false,
      finiteJointHybridEval w f t U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false)
      ∂Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)) ∈ Set.Icc (0 : ℝ) 1 := by
  let ν := Measure.pi (fun _ : Fin (Fintype.card E) => finiteUnitUniform)
  have hinput : Measurable (fun v : Fin (Fintype.card E) → ℝ =>
      (U, finiteSeedExtension (Fintype.card E) V v)) :=
    measurable_const.prodMk (finiteSeedExtension_measurable _ V)
  have hY (r : ℕ) : Measurable (fun v : Fin (Fintype.card E) → ℝ =>
      finiteJointHybridEval w f r U (finiteSeedExtension (Fintype.card E) V v) T ∅ ∅ false) :=
    (finiteJointHybridEval_measurable w f r T ∅ ∅ false).comp hinput
  have hm := (measurable_of_finite g).comp ((hY s).prodMk (hY t))
  have hi := integrable_of_unit_bounds ν hm (fun _ => hg01 _)
  refine ⟨integral_nonneg (fun _ => (hg01 _).1), ?_⟩
  simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun _ => (hg01 _).2)

end
end PottsContinuity.BD12
