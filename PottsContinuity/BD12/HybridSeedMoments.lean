module

public import PottsContinuity.BD12.HybridSeedIdentification
public import PottsContinuity.BD12.HybridFiberSampler
public import PottsContinuity.BD12.DRTConditionalAssociation
public import PottsContinuity.BD12.AugmentedUniformTree
public import PottsContinuity.BD12.FiniteMonotoneSampler
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Actual common-space hybrid moments under fixed original prefixes, now
obtained from the proved joint seed/kernel identification. -/

@[expose] public section

namespace PottsContinuity.BD12
open MeasureTheory PD.FK
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]
    [MeasurableSpace (Finset E)]

/-- The law of a single named common-space hybrid. -/
theorem finiteJointHybridEval_map_seedWindow_single
    (w : Finset E → Set.Ioi (0 : ℝ)) (f : Finset E → ℝ)
    (fixedThrough cutoff : ℕ) (fixedU : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) (hc : fixedThrough ≤ cutoff) :
    (finiteHybridSeedWindow fixedThrough fixedU background R.card n).map
        (fun S => finiteJointHybridEval w f cutoff
          (fun i => (S i).1) (fun i => (S i).2) T HX HY stopped) =
      (finitePinnedLaw w R HY).toMeasure :=
  finiteJointHybridEval_map_seedWindow w f fixedThrough fixedU (fun _ : Unit => cutoff)
    background T HX (fun _ => HY) stopped n hn () hc

/-- Every real observable has its actual pinned expectation on each fixed
prefix of the common-space hybrid construction. -/
theorem finiteJointHybridEval_seedWindow_integral [MeasurableSingletonClass (Finset E)]
    (w : Finset E → Set.Ioi (0 : ℝ)) (f g : Finset E → ℝ)
    (fixedThrough cutoff : ℕ) (fixedU : ℕ → ℝ) (background : ℕ → ℝ × ℝ)
    {R : Finset E} (T : FiniteRevealTree E R) (HX HY : Finset E) (stopped : Bool)
    (n : ℕ) (hn : R.card + n = Fintype.card E) (hc : fixedThrough ≤ cutoff) :
    (∫ S, g (finiteJointHybridEval w f cutoff (fun i => (S i).1) (fun i => (S i).2)
      T HX HY stopped) ∂finiteHybridSeedWindow fixedThrough fixedU background R.card n) =
        finitePinnedMean w R HY g := by
  have hm : Measurable (fun S : ℕ → ℝ × ℝ =>
      finiteJointHybridEval w f cutoff (fun i => (S i).1) (fun i => (S i).2) T HX HY stopped) :=
    (finiteJointHybridEval_measurable w f cutoff T HX HY stopped).comp
      (show Measurable (fun S : ℕ → ℝ × ℝ =>
        ((fun i => (S i).1), (fun i => (S i).2))) by fun_prop)
  rw [← integral_map_of_stronglyMeasurable hm (measurable_of_finite g).stronglyMeasurable,
    finiteJointHybridEval_map_seedWindow_single w f fixedThrough cutoff fixedU background
      T HX HY stopped n hn hc, PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  exact (finitePinnedMean_eq_sum_law w R HY g).symm

variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance drtSeedEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance drtSeedEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

end
end PottsContinuity.BD12
