-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripTopExhaustion.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.CylinderConvergence
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopCylinders
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The canonical sequence of finite FK strip-rectangle laws with wiring only
on the top row, regarded as measures on the common whole-plane carrier. -/
def horizontalStripTopWiredProbabilityMeasures (q : ClusterWeight) (n : ℕ) :
    ℕ → ProbabilityMeasure LatticeConfiguration :=
  fun M => horizontalStripRectangleProbabilityMeasure q M n
    (horizontalStripTopWiredBoundary M n)

theorem horizontalStripTopWiredProbabilityMeasures_monotone_allOpen
    (q : ClusterWeight) (n : ℕ) (F : Finset squareLattice.edgeSet) :
    Monotone (fun M => horizontalStripTopWiredProbabilityMeasures q n M
      (LatticeConfiguration.allOpen F)) := by
  intro M N hMN
  change (((horizontalStripTopWiredProbabilityMeasures q n M : Measure _)
      (LatticeConfiguration.allOpen F)).toNNReal ≤
    ((horizontalStripTopWiredProbabilityMeasures q n N : Measure _)
      (LatticeConfiguration.allOpen F)).toNNReal)
  exact ENNReal.toNNReal_mono (measure_ne_top _ _) <|
    horizontalStripRectangleProbabilityMeasure_allOpen_topWired_mono q n M N hMN F

/-- The canonical increasing-width top-wired laws converge weakly to a unique
probability measure on the whole-plane configuration carrier. -/
theorem horizontalStripTopWiredProbabilityMeasures_existsUnique_limit
    (q : ClusterWeight) (n : ℕ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) := by
  apply probabilityMeasures_tendsto_of_monotone_allOpen
  intro F
  exact horizontalStripTopWiredProbabilityMeasures_monotone_allOpen q n F

/-- Every diverging sequence of horizontal widths has the same weak limit as
the canonical top-wired exhaustion. -/
theorem horizontalStripTopWiredProbabilityMeasures_exhaustions
    (q : ClusterWeight) (n : ℕ) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration,
      Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) ∧
      ∀ M : ℕ → ℕ, Tendsto M atTop atTop →
        Tendsto (fun j => horizontalStripTopWiredProbabilityMeasures q n (M j))
          atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, hμunique⟩ := horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n
  refine ⟨μ, ⟨hμ, ?_⟩, ?_⟩
  · intro M hM
    exact hμ.comp hM
  · intro ν hν
    exact hμunique ν hν.1

end
end PottsContinuity.FKC.Medial
