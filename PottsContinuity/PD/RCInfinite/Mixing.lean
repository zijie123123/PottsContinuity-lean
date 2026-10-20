-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/RCInfinite/Mixing.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.GeneratorMixing
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Separation.Lemmas

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section

/-- On the compact bond space, convergence on all-open generators implies
weak convergence. No monotonicity premise is needed when the limit is given. -/
theorem probabilityMeasures_tendsto_of_allOpen_real {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure LatticeConfiguration} {ν : ProbabilityMeasure LatticeConfiguration}
    (h : ∀ F : Finset Edge, Tendsto
      (fun j => (νs j).toMeasure.real (LatticeConfiguration.allOpen F)) l
      (𝓝 (ν.toMeasure.real (LatticeConfiguration.allOpen F)))) : Tendsto νs l (𝓝 ν) := by
  let κ : ProbabilityMeasure LatticeConfiguration → (Finset Edge → ℝ) :=
    fun η F => η.toMeasure.real (LatticeConfiguration.allOpen F)
  have hcont : Continuous κ := by
    apply continuous_pi
    intro F
    apply continuous_iff_continuousAt.mpr
    intro η
    change Tendsto (fun ζ => κ ζ F) (𝓝 η) (𝓝 (κ η F))
    have hn := LatticeConfiguration.tendsto_allOpen_of_weak
      (μs := fun ζ : ProbabilityMeasure LatticeConfiguration => ζ) (μ := η)
      (l := 𝓝 η) tendsto_id F
    simpa only [κ, ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal,
      Function.comp_def] using (NNReal.continuous_coe.tendsto _).comp hn
  have hinj : Function.Injective κ := by
    intro η ζ heq
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    apply NNReal.coe_injective
    simpa only [κ, ProbabilityMeasure.coeFn_def, Measure.real, ENNReal.toReal] using congrFun heq F
  have hemb : IsClosedEmbedding κ := hcont.isClosedEmbedding hinj
  apply hemb.tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr h

end
end PottsContinuity.PD.RCInfinite
