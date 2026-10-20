module

public import PottsContinuity.PlanarTopology.OpenGraphMonotonicity
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite Filter Topology
noncomputable section

/-- A centered finite box meets the infinite cluster with probability tending
to one whenever an infinite actual component exists almost surely. -/
theorem infiniteHit_box_probability_tendsto_one
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (hinfinite : ∀ᵐ ω ∂μ, ω ∈ infiniteClusterEvent) :
    Tendsto (fun n : ℕ => μ (infiniteHit (latticeBox (0,0) n : Set LatticeVertex))) atTop (𝓝 1) := by
  let E := fun n : ℕ => infiniteHit (latticeBox (0,0) n : Set LatticeVertex)
  have hmono : Monotone E := by
    intro m n hmn ω hω
    obtain ⟨u,hu,hui⟩ := hω
    exact ⟨u,latticeBox_mono (0,0) hmn hu,hui⟩
  have hfull : μ (⋃ n, E n) = 1 := by
    have hae : (⋃ n, E n) =ᵐ[μ] Set.univ := by
      filter_upwards [hinfinite] with ω hω
      obtain ⟨u,hu⟩ := hω
      have hb := subgraph_subset_boxRadius ({u} : Finset LatticeVertex) (Finset.mem_singleton_self u)
      have hm : ω ∈ ⋃ n, E n := Set.mem_iUnion.mpr ⟨_,u,hb,hu⟩
      exact propext ⟨fun _ => Set.mem_univ _,fun _ => hm⟩
    rw [measure_congr hae,measure_univ]
  simpa only [hfull,Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hmono

end
end PottsContinuity.PlanarTopology
