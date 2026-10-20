-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/BoxCompactness.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/BoxCompactness.lean`.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsContinuity.PD.FK.BoxLaw
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

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

namespace PottsContinuity.PD.FK

open MeasureTheory Filter Topology
noncomputable section

/-- The original free FK box PMF on the natural product measurable space. -/
def boxProbabilityMeasure (q : Parameters) (c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨(boxLaw q c r).toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

end
end PottsContinuity.PD.FK
