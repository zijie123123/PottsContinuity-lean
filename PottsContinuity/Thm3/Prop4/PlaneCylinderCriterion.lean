module

public import PottsContinuity.PD.FK.CylinderConvergence
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas

/-! # Weak convergence from the actual all-open cylinder coordinates -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- On the compact original plane configuration carrier, convergence of all
finite all-open cylinders implies genuine weak convergence. -/
theorem plane_tendsto_of_allOpen_real {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure LatticeConfiguration) (ν : ProbabilityMeasure LatticeConfiguration)
    (h : ∀ F : Finset squareLattice.edgeSet,
      Tendsto (fun i => (μs i).toMeasure.real (LatticeConfiguration.allOpen F)) l
        (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F)))) :
    Tendsto μs l (𝓝 ν) := by
  have hκinj : Function.Injective cylinderProbabilityCoordinates := by
    intro μ ρ heq
    exact LatticeConfiguration.probabilityMeasure_eq_of_allOpen (fun F => congrFun heq F)
  have hκembed := continuous_cylinderProbabilityCoordinates.isClosedEmbedding hκinj
  apply hκembed.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro F
  apply NNReal.tendsto_coe.mp
  simpa only [Function.comp_def,cylinderProbabilityCoordinates,ProbabilityMeasure.measureReal_eq_coe_coeFn] using h F

end PottsContinuity.Thm3.Prop4
