module

public import PottsContinuity.PlanarTopology.DualRoleExchange
public import PottsContinuity.PlanarTopology.FiniteClusterArmLimit
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite Filter Topology
open scoped ENNReal
noncomputable section

/-- Every fixed finite set of original half-plane roots has vanishing
probability of an induced-half-plane connection outside growing lattice boxes. -/
theorem halfPlane_arm_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (S : Finset {z : LatticeVertex // 0 ≤ z.1}) :
    Tendsto (fun n : ℕ => μ (sampledGraphArmEvent
      (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}) S
      {v | v.val ∈ latticeBox (0,0) n})) atTop (𝓝 0) := by
  have hG (u v : {z : LatticeVertex // 0 ≤ z.1}) :
      MeasurableSet {ω : LatticeConfiguration |
        ((PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}).Adj u v} :=
    measurableSet_open_adj u.val v.val
  apply sampledGraphArmEvent_probability_tendsto_zero μ _ hG S
  case hF =>
    intro m n hmn v hv
    exact latticeBox_mono (0,0) hmn hv
  case hcover =>
    intro v
    exact ⟨subgraphBoxRadius ({v.val} : Finset LatticeVertex),
      subgraph_subset_boxRadius _ (Finset.mem_singleton_self v.val)⟩
  case hfinite =>
    filter_upwards [halfPlane_no_infinite_cluster_ae μ htranslation hFKG hunique hinfinite] with ω hω
    intro u hu
    exact Set.not_infinite.mp (hω u)

/-- Real probabilities of the same actual half-plane arms also tend to zero. -/
theorem halfPlane_arm_real_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (S : Finset {z : LatticeVertex // 0 ≤ z.1}) :
    Tendsto (fun n : ℕ => μ.real (sampledGraphArmEvent
      (fun ω => (PD.rcInfiniteOpenGraph ω).induce {z : LatticeVertex | 0 ≤ z.1}) S
      {v | v.val ∈ latticeBox (0,0) n})) atTop (𝓝 0) := by
  have hh := ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤) |>.tendsto.comp
    (halfPlane_arm_probability_tendsto_zero μ htranslation hFKG hunique hinfinite S)
  simpa only [Function.comp_def,Measure.real_def,ENNReal.toReal_zero] using hh

end
end PottsContinuity.PlanarTopology
