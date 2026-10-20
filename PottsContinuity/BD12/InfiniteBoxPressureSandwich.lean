module

public import PottsContinuity.BD12.BoxEdgePressureBridge
public import PottsContinuity.BD12.FinitePressureEdgeSandwich

/-! Summed infinite-volume intensities inherit the actual finite surface error. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite MeasureTheory
open scoped BigOperators
noncomputable section
local instance infiniteBoxPressureEdges (n : ℕ) :
    Fintype (boxGraph (0,0) n).edgeSet := Fintype.ofFinite _

/-- Infinite wired intensities summed over box edges are bounded by the
finite free-edge pressure derivative at any larger log activity, plus surface cost. -/
theorem wired_infinite_box_edge_sum_le_free_larger_activity
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ)) (s t : ℝ) (hst : s < t)
    (μ₁ μ₀ : Measure LatticeConfiguration)
    (hμ₁ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature s)).toQ 1 μ₁)
    (hμ₀ : IsRCInfiniteVolumeLimit
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toP
      (drtHomogeneousParameters q hq (drtLogActivityTemperature t)).toQ 0 μ₀)
    (n : ℕ) :
    (∑ e : (boxGraph (0,0) n).edgeSet,
      μ₁.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e})) ≤
    (∑ e : (boxGraph (0,0) n).edgeSet,
      μ₀.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e})) +
      (Nat.card (boxVertexBoundary (0,0) n) : ℝ) * Real.log q / (t-s) := by
  let G := boxGraph (0,0) n
  have hw : (∑ e : G.edgeSet,
      μ₁.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e})) ≤
      drtActivityEdgeSum G q (boxBoundary 1 (0,0) n) s := by
    apply Finset.sum_le_sum
    intro e _
    exact wired_infinite_edge_le_box_mean q hq (drtLogActivityTemperature s) μ₁ hμ₁ n e
  have hf : drtActivityEdgeSum G q (boxBoundary 0 (0,0) n) t ≤
      ∑ e : G.edgeSet,
        μ₀.real (LatticeConfiguration.allOpen {boxEdgeEmbedding (0,0) n e}) := by
    apply Finset.sum_le_sum
    intro e _
    exact free_box_edge_mean_le_infinite q hq (drtLogActivityTemperature t) μ₀ hμ₀ n e
  have heq : drtActivityEdgeSum G q
      (BoundaryCondition.free (boxBoundary 1 (0,0) n).boundary) t =
      drtActivityEdgeSum G q (boxBoundary 0 (0,0) n) t := by
    change drtActivityEdgeSum G q (BoundaryCondition.free (boxVertexBoundary (0,0) n)) t =
      drtActivityEdgeSum G q (BoundaryCondition.free ∅) t
    simp only [drtActivityEdgeSum, drtMean, drtWeight, componentCount, componentSetoid_free]
  have hp := drtActivityEdgeSum_boundary_le_free_larger_activity G q hq
    (boxBoundary 1 (0,0) n) s t hst
  rw [heq] at hp
  change drtActivityEdgeSum G q (boxBoundary 1 (0,0) n) s ≤
    drtActivityEdgeSum G q (boxBoundary 0 (0,0) n) t +
      (Nat.card (boxVertexBoundary (0,0) n) : ℝ) * Real.log q / (t-s) at hp
  exact hw.trans (hp.trans (add_le_add hf le_rfl))

end
end PottsContinuity.BD12
