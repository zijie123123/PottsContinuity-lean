-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightBoundaryLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightFrontier
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

open PottsContinuity.FKC.FiniteFK

/-- Weak convergence to the canonical fixed-height strip law implies convergence
of the probability of the original (untruncated) height-sublevel event. -/
theorem horizontalStripHeightLE_probability_tendsto_of_weak
    {ι : Type*} {L : Filter ι}
    (μs : ι → ProbabilityMeasure LatticeConfiguration)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμs : Tendsto μs L (𝓝 μ))
    (n : ℕ)
    (hfrontier : ((μ : Measure LatticeConfiguration)
      (frontier {ω | horizontalStripHeight n ω 0 ≤ n})) = 0) :
    Tendsto (fun i => ((μs i : Measure LatticeConfiguration)
      {ω | horizontalStripHeight n ω 0 ≤ n})) L
      (𝓝 ((μ : Measure LatticeConfiguration)
        {ω | horizontalStripHeight n ω 0 ≤ n})) := by
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hμs hfrontier

end
end PottsContinuity.FKC.Medial
