module

public import PottsContinuity.Thm3.RSW.StripEventLimit

/-!
# Monotone finite-window event bounds and positivity in the strip

Increasing events evaluated on closed extensions grow with the window. A
concrete finite-window witness therefore gives strictly positive probability
under the actual strip law. This can be used for finitely many small scales,
without assuming a uniform RSW estimate.
-/

@[expose] public section

namespace PottsContinuity.RSW

open MeasureTheory Filter Topology PD.FK

/-- Increasing actual strip events have monotone finite-window probabilities. -/
theorem stripWindowEventProbability_mono (θ : Parameters) (n : ℕ)
    (E : Set (StripConfiguration n)) (hE : IsUpperSet E) :
    Monotone (fun m => stripWindowEventProbability θ n m E) := by
  intro M N hMN
  let G := squareLattice.induce (stripWindow n M : Set (ℤ × ℤ))
  let H := squareLattice.induce (stripWindow n N : Set (ℤ × ℤ))
  let f := stripWindowEmbedding (n := n) hMN
  let S : Set (Configuration G) :=
    {C | stripPlaneRestriction n (stripWindowPlaneConfiguration n M C) ∈ E}
  have hS : IsUpperSet S := by
    intro A B hAB hA
    exact hE (fun e => stripWindowPlaneConfiguration_mono n M hAB
      ((stripPlaneEmbedding n).mapEdgeSet e)) hA
  have hprob := embedded_boundary_probability_le G H f (stripWindow_map_le hMN)
    θ (stripWindowBoundary n N 0) S hS
  have hinner : measure G θ
      (isolatedExtensionPullbackBoundary f (stripWindowBoundary n N 0)) S =
        measure G θ (stripWindowBoundary n M 0) S := by
    unfold PD.FK.measure
    rw [law_eq_of_boundary_partition_eq (G := G) θ _ _
      (stripWindow_top_pullback_partition hMN)]
  rw [hinner] at hprob
  change (measure G θ (stripWindowBoundary n M 0) S).toReal ≤ _
  apply hprob.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro C hC
  apply hE (show stripPlaneRestriction n (stripWindowPlaneConfiguration n M
      (embeddedConfigurationRestriction G H f (stripWindow_map_le hMN) C)) ≤
      stripPlaneRestriction n (stripWindowPlaneConfiguration n N C) from
    fun e => stripWindowPlaneConfiguration_restrict_le hMN C
      ((stripPlaneEmbedding n).mapEdgeSet e)) hC

/-- Every finite-window probability is a lower bound for the actual limit,
when the event is clopen and increasing. -/
theorem stripWindowEventProbability_le_limit (θ : Parameters) (n m : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E) :
    stripWindowEventProbability θ n m E ≤ μ.real E := by
  apply strip_event_lower_of_finite_window_bounds θ n μ hμ E hclopen
  filter_upwards [eventually_ge_atTop m] with M hM
  exact stripWindowEventProbability_mono θ n E hupper hM

/-- A concrete finite-window witness gives positive strip-event probability.
The fixed finite scale does not provide a scale-independent RSW lower bound. -/
theorem strip_event_pos_of_finite_window_witness (θ : Parameters) (n m : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E)
    (C : Configuration (squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))))
    (hC : stripPlaneRestriction n (stripWindowPlaneConfiguration n m C) ∈ E) :
    0 < μ.real E := by
  have hpos : 0 < stripWindowEventProbability θ n m E := by
    unfold stripWindowEventProbability
    rw [ENNReal.toReal_pos_iff]
    constructor
    · rw [measure_pos_iff]
      exact ⟨C, hC⟩
    · exact measure_lt_top _ _
  exact lt_of_lt_of_le hpos
    (stripWindowEventProbability_le_limit θ n m μ hμ E hclopen hupper)

end PottsContinuity.RSW
