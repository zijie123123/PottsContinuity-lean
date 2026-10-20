-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/BoxCompactness.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.BoxLaw
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences

/-!
# Subsequence compactness for the actual finite-box configuration laws

The whole-lattice edge-state space is a countable product of the discrete finite
space Bool. Its probability measures carry their usual topology of weak
convergence. Complete mathlib compactness and metrizability theorems yield
subsequential limits for the actual closed-extended box laws. No uniqueness or
full-volume convergence is claimed here, and this is not tightness of rescaled
interface curves or loop collections.
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory Filter Topology
noncomputable section

/-- The original free FK box PMF on the natural product measurable space. -/
def boxProbabilityMeasure (q : ClusterWeight) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨(boxLaw q c r).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

end
end PottsContinuity.FKC.FiniteFK
