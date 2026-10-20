module

public import PottsContinuity.Thm3.RSW.StripTranslatedWindowState

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section

/-- Translating an inner top-wired window into a larger one dominates every
increasing event of the original closed strip extension. -/
theorem stripWindowEventProbability_translation_le
    (θ : Parameters) (n M N : ℕ) (c : ℤ) (hMN : M+c.natAbs ≤ N)
    (E : Set (StripConfiguration n)) (hE : IsUpperSet E) :
    stripWindowEventProbability θ n M E ≤ stripWindowEventProbability θ n N
      ((stripHorizontalTranslationConfiguration n (-c)) ⁻¹' E) := by
  let S : Set (Configuration (PottsContinuity.squareLattice.induce
      (stripWindow n M : Set (ℤ × ℤ)))) :=
    {C | stripPlaneRestriction n (stripWindowPlaneConfiguration n M C) ∈ E}
  have hS : IsUpperSet S := by
    intro C D hCD hC
    exact hE (fun e => stripWindowPlaneConfiguration_mono n M hCD
      ((stripPlaneEmbedding n).mapEdgeSet e)) hC
  have hp := stripWindow_translated_probability_le n M N c hMN θ S hS
  apply hp.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro C hC
  exact hE (stripWindow_translated_restriction_le n M N c hMN C) hC

/-- Every genuine top-only strip limit satisfies horizontal translation
domination for clopen increasing events, at every interior parameter. -/
theorem strip_limit_clopen_translation_domination
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E) :
    μ.real E ≤ μ.real ((stripHorizontalTranslationConfiguration n (-c)) ⁻¹' E) := by
  have hsource := stripWindowEventProbability_tendsto θ n μ hμ E hclopen
  have htarget := stripWindowEventProbability_tendsto θ n μ hμ
    ((stripHorizontalTranslationConfiguration n (-c)) ⁻¹' E)
    (hclopen.preimage (stripHorizontalTranslationConfiguration n (-c)).continuous)
  have hN : Tendsto (fun M : ℕ => M+c.natAbs) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  apply le_of_tendsto_of_tendsto hsource (htarget.comp hN)
  exact Eventually.of_forall (fun M =>
    stripWindowEventProbability_translation_le θ n M (M+c.natAbs) c le_rfl E hupper)

end
end PottsContinuity.RSW
