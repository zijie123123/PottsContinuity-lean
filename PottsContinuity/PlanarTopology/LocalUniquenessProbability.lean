module

public import PottsContinuity.PlanarTopology.LocalUniquenessExhaustion
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- Almost-sure global uniqueness implies high-probability finite local
uniqueness along box exhaustion, for every fixed finite marked set. -/
theorem local_uniqueness_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω) (S : Finset LatticeVertex) :
    Tendsto (fun n : ℕ => μ (finiteLocalUniquenessEvent S (S ∪ latticeBox (0,0) n)))
      atTop (𝓝 1) := by
  let E := fun n : ℕ => finiteLocalUniquenessEvent S (S ∪ latticeBox (0,0) n)
  have hfull : μ (⋃ n, E n) = 1 := by
    have hae : (⋃ n, E n) =ᵐ[μ] Set.univ := by
      filter_upwards [hunique] with ω hω
      have hh := unique_cluster_eventually_local_unique ω hω S
      obtain ⟨n,hn⟩ := eventually_atTop.mp hh
      have hm : ω ∈ ⋃ n, E n := Set.mem_iUnion.mpr ⟨n,hn n le_rfl⟩
      exact propext ⟨fun _ => Set.mem_univ _,fun _ => hm⟩
    rw [measure_congr hae,measure_univ]
  have hmono : Monotone E := finiteLocalUniquenessEvent_box_monotone S
  simpa only [hfull,Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono

/-- The corresponding real probability limit, retaining the same explicit events. -/
theorem local_uniqueness_real_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster ω) (S : Finset LatticeVertex) :
    Tendsto (fun n : ℕ => (μ (finiteLocalUniquenessEvent S (S ∪ latticeBox (0,0) n))).toReal)
      atTop (𝓝 1) := by
  have hh := ENNReal.continuousAt_toReal (show (1 : ℝ≥0∞) ≠ ⊤ by simp)
  simpa only [Function.comp_def,ENNReal.toReal_one] using hh.tendsto.comp (local_uniqueness_probability_tendsto_one μ hunique S)

end
end PottsContinuity.PlanarTopology
