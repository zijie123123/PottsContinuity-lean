module

public import PottsContinuity.Thm3.RSW.StripTranslationDomination
public import PottsContinuity.Thm3.RSW.BooleanCylinderDetermination

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- Inverse translation gives equality on every clopen increasing strip event. -/
theorem strip_limit_clopen_translation_eq
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E) :
    μ.real E = μ.real ((stripHorizontalTranslationConfiguration n c) ⁻¹' E) := by
  have hforward := strip_limit_clopen_translation_domination θ n (-c) μ hμ E hclopen hupper
  simp only [neg_neg] at hforward
  have hpreupper : IsUpperSet ((stripHorizontalTranslationConfiguration n c) ⁻¹' E) := by
    intro ω η h hω
    exact hupper (stripHorizontalTranslationConfiguration_monotone n c h) hω
  have hreverse := strip_limit_clopen_translation_domination θ n c μ hμ
    ((stripHorizontalTranslationConfiguration n c) ⁻¹' E)
    (hclopen.preimage (stripHorizontalTranslationConfiguration n c).continuous) hpreupper
  have heq : (stripHorizontalTranslationConfiguration n (-c)) ⁻¹'
      ((stripHorizontalTranslationConfiguration n c) ⁻¹' E) = E := by
    ext ω
    change stripHorizontalTranslationConfiguration n c
      (stripHorizontalTranslationConfiguration n (-c) ω) ∈ E ↔ ω ∈ E
    have hcancel := stripHorizontalTranslationConfiguration_neg_cancel n (-c) ω
    exact iff_of_eq (by simpa only [neg_neg] using congrArg (fun η => η ∈ E) hcancel)
  rw [heq] at hreverse
  exact le_antisymm hforward hreverse

/-- The whole genuine top-only strip law is invariant under every horizontal
integer translation, for all admissible FK parameters. -/
theorem strip_limit_horizontalTranslation_invariant
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ) :
    μ.map (stripHorizontalTranslationConfiguration n c) = μ := by
  let stripTranslationProbability : IsProbabilityMeasure μ := hμ.1
  have hm := (stripHorizontalTranslationConfiguration n c).continuous.measurable
  let stripTranslatedProbability : IsProbabilityMeasure
      (μ.map (stripHorizontalTranslationConfiguration n c)) :=
    inferInstance
  apply boolean_measure_eq_of_allOpen
  intro F
  let E : Set (StripConfiguration n) := {ω | ∀ e ∈ F, ω e = true}
  have hE : IsClopen E := strip_isClopen_of_finite_support n F E (by
    intro ω η h
    exact ⟨fun hω e he => (h e he).symm.trans (hω e he),
      fun hη e he => (h e he).trans (hη e he)⟩)
  have hup : IsUpperSet E := by
    intro ω η h hω e he
    exact Bool.le_iff_imp.mp (h e) (hω e he)
  change (μ.map (stripHorizontalTranslationConfiguration n c)) E = μ E
  rw [Measure.map_apply hm hE.isOpen.measurableSet]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (strip_limit_clopen_translation_eq θ n c μ hμ E hE hup).symm

/-- The self-dual strip measure has the whole-law translation identity needed
by the original source-square seed transport. -/
theorem selfDualStripMeasure_horizontalTranslation_invariant
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (c : ℤ) :
    (selfDualStripMeasure q n).map (stripHorizontalTranslationConfiguration n c) =
      selfDualStripMeasure q n :=
  strip_limit_horizontalTranslation_invariant (selfDualParameters q) n c _
    (selfDualStripMeasure_isLimit q n)

end
end PottsContinuity.RSW
