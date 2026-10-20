module

public import PottsContinuity.Thm4Plane.ScreenPlaneAssembly
public import PottsContinuity.Thm4Plane.ScreenBoundaryClusterConditional
public import PottsContinuity.Thm4Records.ConnectorFactor

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open PottsContinuity.FKC.FiniteFK

noncomputable section

attribute [local instance] PottsContinuity.PD.FK.configurationMeasurableSpace

/-- The side probability estimate and the unconditional connector factor give
the explicit self-dual logarithmic limit. -/
theorem theorem_four_at_self_dual_of_sideFactor
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (hside : ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      c₂ ^ 2 * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m))) :
    ∃ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ ∧
      Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y})) atTop (𝓝 0) := by
  obtain ⟨c₂, hc₂, hF⟩ := hside
  have hC : ∀ m : ℕ, 1 ≤ m →
      (1 / (1 + q ^ 2)) * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          ((slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ∩
              slitScreenConnectorEvent m) := by
    intro m hm
    exact PottsContinuity.Thm4Records.slitScreenConnectorFactor
      ⟨q, hq⟩ m hm
  exact theorem_four_at_self_dual_of_source_screen_interfaces
    q hq c₂ hc₂ hF hC
    (fun p μ hp hμ m hm =>
      slitScreen_joint_connector_probability_le_free_plane
        ⟨q, hq⟩ m hm p hp μ hμ)

end
end PottsContinuity.Thm4Plane
