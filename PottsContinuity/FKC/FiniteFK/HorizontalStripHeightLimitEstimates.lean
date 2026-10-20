-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightLimitEstimates.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutClopen
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutProbability
public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalCutAlmostSure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC.FiniteFK
noncomputable section

/-- At fixed strip height and local-cut radius, the two actual finite height
masses together with the actual local-cut failure mass converge to their
canonical counterparts. -/
theorem horizontalStripHeightLimit_three_mass_estimate
    (q : PottsContinuity.FKC.ClusterWeight) (n M : ℕ) :
    Tendsto
      (fun N : ℕ =>
        (((horizontalStripTopWiredProbabilityMeasures q n N : Measure LatticeConfiguration)
          {ω | horizontalStripHeight n ω 0 ≤ n}).toReal +
        ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
          Measure LatticeConfiguration)
          {ω | horizontalStripHeight n ω 0 ≤ n}).toReal +
        ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
          Measure LatticeConfiguration)
          (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal))
      atTop
      (𝓝 (
        2 * ((((Classical.choose
          (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n) :
            ProbabilityMeasure LatticeConfiguration) : Measure LatticeConfiguration)
          {ω | horizontalStripHeight n ω 0 ≤ n}).toReal) +
        (((Classical.choose
          (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n) :
            ProbabilityMeasure LatticeConfiguration) : Measure LatticeConfiguration)
          (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal)) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)
  let H : Set LatticeConfiguration := {ω | horizontalStripHeight n ω 0 ≤ n}
  let F : Set LatticeConfiguration := (horizontalStripLocalClosedCutSuccess M n)ᶜ
  have hweak : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ) := by
    simpa [μ] using
      (Classical.choose_spec
        (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)).1
  have hweakAsym : Tendsto (horizontalStripAsymmetricTopSidesProbabilityMeasures q n)
      atTop (𝓝 μ) := by
    simpa [μ] using horizontalStripAsymmetricTopSidesProbabilityMeasures_tendsto_canonical q n
  have hfront : (μ : Measure LatticeConfiguration) (frontier H) = 0 := by
    simpa [μ, H] using horizontalStripHeightLE_frontier_measure_zero q n _ hweak
  have hcenterMeasure :=
    horizontalStripHeightLE_probability_tendsto_of_weak
      (horizontalStripTopWiredProbabilityMeasures q n) μ hweak n hfront
  have hasymMeasure :=
    horizontalStripHeightLE_probability_tendsto_of_weak
      (horizontalStripAsymmetricTopSidesProbabilityMeasures q n) μ hweakAsym n hfront
  have hclopen : IsClopen F := by
    simpa [F] using (isClopen_horizontalStripLocalClosedCutSuccess M n).compl
  have hfailMeasure : Tendsto
      (fun N : ℕ => (horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
        Measure LatticeConfiguration) F) atTop
      (𝓝 ((μ : Measure LatticeConfiguration) F)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweakAsym (by
      simp [hclopen])
  have hcenter : Tendsto
      (fun N : ℕ => ((horizontalStripTopWiredProbabilityMeasures q n N :
        Measure LatticeConfiguration) H).toReal) atTop
      (𝓝 (((μ : Measure LatticeConfiguration) H).toReal)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure LatticeConfiguration) H)).comp
      hcenterMeasure
  have hasym : Tendsto
      (fun N : ℕ => ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
        Measure LatticeConfiguration) H).toReal) atTop
      (𝓝 (((μ : Measure LatticeConfiguration) H).toReal)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure LatticeConfiguration) H)).comp
      hasymMeasure
  have hfail : Tendsto
      (fun N : ℕ => ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N :
        Measure LatticeConfiguration) F).toReal) atTop
      (𝓝 (((μ : Measure LatticeConfiguration) F).toReal)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure LatticeConfiguration) F)).comp
      hfailMeasure
  have hsum := hcenter.add (hasym.add hfail)
  convert hsum using 1 <;> simp [H, F, μ] <;> ring_nf

/-- The canonical fixed-height error term tends to zero as the local-cut
radius grows. -/
theorem horizontalStripHeightLimit_failure_mass_tendsto_zero
    (q : PottsContinuity.FKC.ClusterWeight) (n : ℕ) :
    Tendsto
      (fun M : ℕ => ((((Classical.choose
        (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n) :
          ProbabilityMeasure LatticeConfiguration) : Measure LatticeConfiguration)
        (horizontalStripLocalClosedCutSuccess M n)ᶜ).toReal))
      atTop (𝓝 0) := by
  exact tendsto_horizontalStripLocalClosedCutFailure_probability_zero q n _
    (Classical.choose_spec
      (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)).1

end
end PottsContinuity.FKC.Medial
