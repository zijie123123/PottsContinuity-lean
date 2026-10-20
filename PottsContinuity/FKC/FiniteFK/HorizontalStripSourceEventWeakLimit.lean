-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripSourceEventWeakLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEventClopen
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopExhaustion
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

/-- Weak convergence preserves the probability of the literal fixed-point
GoodEvent, which is clopen in the natural whole-plane product topology. -/
theorem tendsto_horizontalStripGoodEventProbability_of_weak
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure LatticeConfiguration}
    {μ : ProbabilityMeasure LatticeConfiguration}
    (hμ : Tendsto μs l (𝓝 μ))
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    Tendsto (fun i => μs i (horizontalStripGoodEvent n m k h hh)) l
      (𝓝 (μ (horizontalStripGoodEvent n m k h hh))) :=
  ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (isClopen_horizontalStripGoodEvent n m k h hh)

/-- Weak convergence preserves the probability of the literal SourceA event. -/
theorem tendsto_horizontalStripSourceAEventProbability_of_weak
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure LatticeConfiguration}
    {μ : ProbabilityMeasure LatticeConfiguration}
    (hμ : Tendsto μs l (𝓝 μ))
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    Tendsto (fun i => μs i (horizontalStripSourceAEvent n m k h hh)) l
      (𝓝 (μ (horizontalStripSourceAEvent n m k h hh))) :=
  ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (isClopen_horizontalStripSourceAEvent n m k h hh)

theorem tendsto_horizontalStripSourceAEvent_toRealProbability_of_weak
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure LatticeConfiguration}
    {μ : ProbabilityMeasure LatticeConfiguration}
    (hμ : Tendsto μs l (𝓝 μ))
    (n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) :
    Tendsto (fun i => ((μs i (horizontalStripSourceAEvent n m k h hh) : NNReal) : ℝ)) l
      (𝓝 ((μ (horizontalStripSourceAEvent n m k h hh) : NNReal) : ℝ)) := by
  exact (NNReal.continuous_coe.tendsto _).comp
    (tendsto_horizontalStripSourceAEventProbability_of_weak hμ n m k h hh)

/-- The canonical top-wired laws have a unique common weak limit, and every
fixed GoodEvent or SourceA probability converges to its value under that same
measure along every diverging sequence of widths. The measure is quantified
before all local event parameters and width sequences. -/
theorem horizontalStripTopWired_common_limit_event_probabilities
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) ∧
      ∀ (m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n) (M : ℕ → ℕ),
        Tendsto M atTop atTop →
          Tendsto (fun j => horizontalStripTopWiredProbabilityMeasures q n (M j)
            (horizontalStripGoodEvent n m k h hh)) atTop
            (𝓝 (μ (horizontalStripGoodEvent n m k h hh))) ∧
          Tendsto (fun j => horizontalStripTopWiredProbabilityMeasures q n (M j)
            (horizontalStripSourceAEvent n m k h hh)) atTop
            (𝓝 (μ (horizontalStripSourceAEvent n m k h hh))) := by
  obtain ⟨μ, hprop, hunique⟩ := horizontalStripTopWiredProbabilityMeasures_exhaustions q n
  refine ⟨μ, ⟨hprop.1, ?_⟩, ?_⟩
  · intro m k h hh M hM
    have hweak := hprop.2 M hM
    exact ⟨tendsto_horizontalStripGoodEventProbability_of_weak hweak n m k h hh,
      tendsto_horizontalStripSourceAEventProbability_of_weak hweak n m k h hh⟩
  · intro ν hν
    exact tendsto_nhds_unique hν.1 hprop.1

end
end PottsContinuity.FKC.Medial
