module

public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm4Plane.LogarithmicLimit16
public import PottsContinuity.Thm4Plane.PlaneTranslation
public import PottsContinuity.Thm4Plane.ExplicitLimit

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm4Plane

open PottsContinuity
open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance screenPlaneConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration (slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

/-- Conditional Theorem 4 assembly from the two finite screen factors and the
free-interior transfer for their literal joint screen event. The factors and
transfer remain explicit premises; this theorem does not discharge them. -/
theorem theorem_four_at_self_dual_of_screen_factors_and_plane_transfer
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hF : ∀ m : ℕ, 1 ≤ m →
      b * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)))
    (hC : ∀ m : ℕ, 1 ≤ m →
      d * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          ((slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ∩
              slitScreenConnectorEvent m))
    (hplane : ∀ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) →
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ →
      ∀ m : ℕ, 1 ≤ m →
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
              slitScreenConnectorEvent m) ≤
          μ.real (translatedBoxBoundaryConnectionEvent (0, -(16 * (m : ℤ))) m)) :
    ∃ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ ∧
      Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y})) atTop (𝓝 0) := by
  obtain ⟨p, μ, hp, hμ⟩ := exists_self_dual_free_limit q hq
  obtain ⟨c, hc, hscreen⟩ :=
    slitScreenFourFactor_probability_lower_bound_of_crossing_factors
      ⟨q, hq⟩ b d (le_of_lt hb) (le_of_lt hd) hF hC
  have hpoly : ∀ m : ℕ, 1 ≤ m →
      (c * b * d) / ((16 * m : ℕ) : ℝ)^16 ≤
        μ.real {ω | ∃ y ∈ vertexBoundary (box m),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y} := by
    intro m hm
    have hscreen' := hscreen m hm
    have hplane' := hplane p μ hp hμ m hm
    have htranslate := translatedBoxBoundaryConnection_probability_eq
      p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ hq.1 μ hμ
      (0, -(16 * (m : ℤ))) m
    calc
      (c * b * d) / ((16 * m : ℕ) : ℝ)^16 =
          (c / ((16 * m : ℕ) : ℝ)^16) * b * d := by ring
      _ ≤ (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
              slitScreenConnectorEvent m) := hscreen'
      _ ≤ μ.real (translatedBoxBoundaryConnectionEvent
          (0, -(16 * (m : ℤ))) m) := hplane'
      _ = μ.real {ω | ∃ y ∈ vertexBoundary (box m),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y} := by
        rw [htranslate]
        rfl
  have hlog := boxBoundary_logarithmic_rate_zero_of_sixteen_scale_polynomial_lower_bound
    p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ μ hμ (c * b * d)
    (mul_pos (mul_pos hc hb) hd) hpoly
  exact ⟨p, μ, hp, hμ, hlog⟩

/-- Source-factor version of the conditional plane assembly. The two finite
crossing assumptions are exactly the paired side-crossing factor `c₂²` and the
connector factor `1/(1+q²)`; the remaining premise is the free-interior
transfer for the source connector event. -/
theorem theorem_four_at_self_dual_of_source_screen_interfaces
    (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4)
    (c₂ : ℝ) (hc₂ : 0 < c₂)
    (hF : ∀ m : ℕ, 1 ≤ m →
      c₂ ^ 2 * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real (slitScreenEvent m) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)))
    (hC : ∀ m : ℕ, 1 ≤ m →
      (1 / (1 + q ^ 2)) * (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ≤
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          ((slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m)) ∩
              slitScreenConnectorEvent m))
    (hplane : ∀ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) →
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ →
      ∀ m : ℕ, 1 ≤ m →
        (slitScreenFiniteMeasure ⟨q, hq⟩ m).real
          (slitScreenEvent m ∩
            (slitScreenLeftCrossingEvent m ∩ slitScreenRightCrossingEvent m) ∩
              slitScreenConnectorEvent m) ≤
          μ.real (translatedBoxBoundaryConnectionEvent (0, -(16 * (m : ℤ))) m)) :
    ∃ (p : Set.Icc (0 : ℝ) 1)
      (μ : Measure (squareLattice.edgeSet → Bool)),
      (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q) ∧
      IsRCInfiniteVolumeLimit p ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 0 μ ∧
      Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y})) atTop (𝓝 0) := by
  have hb : 0 < c₂ ^ 2 := sq_pos_of_pos hc₂
  have hd : 0 < 1 / (1 + q ^ 2) := by positivity
  exact theorem_four_at_self_dual_of_screen_factors_and_plane_transfer
    q hq (c₂ ^ 2) (1 / (1 + q ^ 2)) hb hd hF hC hplane

end
end PottsContinuity.Thm4Plane
