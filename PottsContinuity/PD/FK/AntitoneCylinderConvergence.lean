-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/AntitoneCylinderConvergence.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/CylinderConvergence.lean`.
The monotone cylinder argument is adapted to antitone cylinder probabilities. -/
module

public import PottsContinuity.PD.FK.CylinderConvergence
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Lemmas

@[expose] public section

open Set MeasureTheory Filter Topology

namespace PottsContinuity.PD.FK

noncomputable section

/-- If every finite all-open cylinder probability is antitone along a sequence,
then the sequence converges weakly to a unique probability measure. -/
theorem probabilityMeasures_tendsto_of_antitone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hanti : ∀ F : Finset squareLattice.edgeSet,
      Antitone (fun n => μs n (LatticeConfiguration.allOpen F))) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq μs
  have hlimit (F : Finset squareLattice.edgeSet) :
      μ (LatticeConfiguration.allOpen F) =
        ⨅ n, μs n (LatticeConfiguration.allOpen F) := by
    let f : ℕ → NNReal := fun n => μs n (LatticeConfiguration.allOpen F)
    have hf : Antitone f := hanti F
    have hbounded : BddBelow (Set.range f) := ⟨0, fun _ _ => zero_le⟩
    have ht := tendsto_atTop_ciInf hf hbounded
    have hsub := ht.comp hφ.tendsto_atTop
    have hweakF := LatticeConfiguration.tendsto_allOpen_of_weak hweak F
    exact tendsto_nhds_unique hweakF hsub
  let κ := cylinderProbabilityCoordinates
  have hκcont : Continuous κ := continuous_cylinderProbabilityCoordinates
  have hκinj : Function.Injective κ := by
    intro μ₁ μ₂ h
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    exact congrFun h F
  have hκembed : IsClosedEmbedding κ := hκcont.isClosedEmbedding hκinj
  have hκtendsto : Tendsto (fun n => κ (μs n)) atTop (𝓝 (κ μ)) := by
    apply tendsto_pi_nhds.2
    intro F
    let f : ℕ → NNReal := fun n => μs n (LatticeConfiguration.allOpen F)
    have hf : Antitone f := hanti F
    have hbounded : BddBelow (Set.range f) := ⟨0, fun _ _ => zero_le⟩
    have ht := tendsto_atTop_ciInf hf hbounded
    change Tendsto f atTop (𝓝 (μ (LatticeConfiguration.allOpen F)))
    rw [hlimit F]
    exact ht
  have hfull : Tendsto μs atTop (𝓝 μ) := hκembed.tendsto_nhds_iff.mpr hκtendsto
  refine ⟨μ, hfull, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hfull

end
end PottsContinuity.PD.FK
