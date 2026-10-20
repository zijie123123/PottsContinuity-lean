-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/CylinderConvergenceCriterion.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.CylinderConvergence

@[expose] public section

open Filter Topology MeasureTheory

namespace PottsContinuity.FKC.FiniteFK

/-- Weak convergence of probability measures on the whole-plane configuration
space is equivalent to convergence of every finite all-open cylinder
coordinate. -/
theorem probabilityMeasures_tendsto_iff_allOpen_coordinates
    {ι : Type*} {l : Filter ι} (μs : ι → ProbabilityMeasure LatticeConfiguration)
    (μ : ProbabilityMeasure LatticeConfiguration) :
    Tendsto μs l (𝓝 μ) ↔
      ∀ F : Finset squareLattice.edgeSet,
        Tendsto (fun i => μs i (LatticeConfiguration.allOpen F)) l
          (𝓝 (μ (LatticeConfiguration.allOpen F))) := by
  constructor
  · intro hμ F
    exact LatticeConfiguration.tendsto_allOpen_of_weak hμ F
  · intro hcoords
    let κ := cylinderProbabilityCoordinates
    have hκcont : Continuous κ := continuous_cylinderProbabilityCoordinates
    have hκinj : Function.Injective κ := by
      intro μ₁ μ₂ h
      apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
      intro F
      exact congrFun h F
    have hκembed : IsClosedEmbedding κ := hκcont.isClosedEmbedding hκinj
    have hκtendsto : Tendsto (fun i => κ (μs i)) l (𝓝 (κ μ)) := by
      apply tendsto_pi_nhds.2
      intro F
      exact hcoords F
    exact hκembed.tendsto_nhds_iff.mpr hκtendsto

end PottsContinuity.FKC.FiniteFK
