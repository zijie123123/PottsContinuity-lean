module

public import PottsContinuity.PlanarTopology.RectangleHalfPlaneArms
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.FK.Medial PD.RCInfinite BD12 Filter Topology
noncomputable section

/-- A fixed-height horizontal rectangle crossing has probability tending
to zero as its width grows, under actual dual unique existing infinity. -/
theorem horizontalRectangle_fixed_height_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (K : ℕ) :
    Tendsto (fun n : ℕ => μ (horizontalRectangle (0,0) (n+1) K)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (halfPlane_arm_probability_tendsto_zero μ htranslation hFKG hunique hinfinite (halfPlaneRectangleSeeds 0 K))
  · intro n
    exact zero_le
  · intro n
    exact measure_mono (horizontalRectangle_subset_halfPlaneArm n K)

/-- A fixed-width vertical rectangle crossing likewise vanishes as its
height grows. This is a genuine finite-rectangle event with no wiring. -/
theorem verticalRectangle_fixed_width_probability_tendsto_zero
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (htranslation : ∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ)
    (hFKG : ∀ A B : Set LatticeConfiguration, MeasurableSet A → MeasurableSet B →
      IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B))
    (hunique : ∀ᵐ ω ∂μ, atMostOneInfiniteCluster (wholePlaneDualConfigurationHomeomorph ω))
    (hinfinite : ∀ᵐ ω ∂μ, wholePlaneDualConfigurationHomeomorph ω ∈ infiniteClusterEvent)
    (W : ℕ) :
    Tendsto (fun n : ℕ => μ (verticalRectangle (0,0) W (n+1))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (halfPlane_arm_probability_tendsto_zero μ htranslation hFKG hunique hinfinite (halfPlaneRectangleSeeds W 0))
  · intro n
    exact zero_le
  · intro n
    exact measure_mono (verticalRectangle_subset_halfPlaneArm n W)

end
end PottsContinuity.PlanarTopology
