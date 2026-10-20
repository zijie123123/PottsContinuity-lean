module

public import PottsContinuity.Thm3.RSW.StripReflectedWindowState

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section

/-- Reflecting an inner top-wired window into a larger one dominates every
increasing event of the original closed strip extension. -/
theorem stripWindowEventProbability_reflection_le
    (θ : Parameters) (n M N : ℕ) (c : ℤ) (hMN : M+c.natAbs ≤ N)
    (E : Set (StripConfiguration n)) (hE : IsUpperSet E) :
    stripWindowEventProbability θ n M E ≤ stripWindowEventProbability θ n N
      ((stripHorizontalReflectionConfiguration n c) ⁻¹' E) := by
  let S : Set (Configuration (PottsContinuity.squareLattice.induce
      (stripWindow n M : Set (ℤ × ℤ)))) :=
    {C | stripPlaneRestriction n (stripWindowPlaneConfiguration n M C) ∈ E}
  have hS : IsUpperSet S := by
    intro C D hCD hC
    exact hE (fun e => stripWindowPlaneConfiguration_mono n M hCD
      ((stripPlaneEmbedding n).mapEdgeSet e)) hC
  let f := stripWindowReflectionEmbedding n M N c hMN
  have hmap := stripWindowReflection_graph_le n M N c hMN
  have hp := embedded_boundary_probability_le _ _ f hmap θ (stripWindowBoundary n N 0) S hS
  have heq : measure (PottsContinuity.squareLattice.induce
      (stripWindow n M : Set (ℤ × ℤ))) θ
      (isolatedExtensionPullbackBoundary f (stripWindowBoundary n N 0)) =
      measure (PottsContinuity.squareLattice.induce
        (stripWindow n M : Set (ℤ × ℤ))) θ (stripWindowBoundary n M 0) := by
    unfold PD.FK.measure
    rw [law_eq_of_boundary_partition_eq θ _ _
      (stripWindow_reflected_top_pullback_partition n M N c hMN)]
  rw [heq] at hp
  apply hp.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro C hC
  exact hE (stripWindow_reflected_restriction_le n M N c hMN C) hC

/-- Every genuine top-only strip limit satisfies horizontal reflection
domination for clopen increasing events, at every interior parameter. -/
theorem strip_limit_clopen_reflection_domination
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E) :
    μ.real E ≤ μ.real ((stripHorizontalReflectionConfiguration n c) ⁻¹' E) := by
  have hsource := stripWindowEventProbability_tendsto θ n μ hμ E hclopen
  have htarget := stripWindowEventProbability_tendsto θ n μ hμ
    ((stripHorizontalReflectionConfiguration n c) ⁻¹' E)
    (hclopen.preimage (stripHorizontalReflectionConfiguration n c).continuous)
  have hN : Tendsto (fun M : ℕ => M+c.natAbs) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  apply le_of_tendsto_of_tendsto hsource (htarget.comp hN)
  exact Eventually.of_forall (fun M =>
    stripWindowEventProbability_reflection_le θ n M (M+c.natAbs) c le_rfl E hupper)

end
end PottsContinuity.RSW
