module

public import PottsContinuity.Thm3.RSW.StripReflectionDomination
public import PottsContinuity.Thm3.RSW.BooleanCylinderDetermination

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- Repeated reflection gives equality on every clopen increasing strip event. -/
theorem strip_limit_clopen_reflection_eq
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ)
    (E : Set (StripConfiguration n)) (hclopen : IsClopen E) (hupper : IsUpperSet E) :
    μ.real E = μ.real ((stripHorizontalReflectionConfiguration n c) ⁻¹' E) := by
  have hforward := strip_limit_clopen_reflection_domination θ n c μ hμ E hclopen hupper
  have hpreupper : IsUpperSet ((stripHorizontalReflectionConfiguration n c) ⁻¹' E) := by
    intro ω η h hω
    exact hupper (stripHorizontalReflectionConfiguration_monotone n c h) hω
  have hreverse := strip_limit_clopen_reflection_domination θ n c μ hμ
    ((stripHorizontalReflectionConfiguration n c) ⁻¹' E)
    (hclopen.preimage (stripHorizontalReflectionConfiguration n c).continuous) hpreupper
  have heq : (stripHorizontalReflectionConfiguration n c) ⁻¹'
      ((stripHorizontalReflectionConfiguration n c) ⁻¹' E) = E := by
    ext ω
    change stripHorizontalReflectionConfiguration n c
      (stripHorizontalReflectionConfiguration n c ω) ∈ E ↔ ω ∈ E
    rw [stripHorizontalReflectionConfiguration_involutive n c ω]
  rw [heq] at hreverse
  exact le_antisymm hforward hreverse

/-- The whole genuine top-only strip law is invariant under every horizontal
integer reflection, for all admissible FK parameters. -/
theorem strip_limit_horizontalReflection_invariant
    (θ : Parameters) (n : ℕ) (c : ℤ) (μ : Measure (StripConfiguration n))
    (hμ : IsTopWiredStripLimit θ n 0 μ) :
    μ.map (stripHorizontalReflectionConfiguration n c) = μ := by
  let stripReflectionProbability : IsProbabilityMeasure μ := hμ.1
  have hm := (stripHorizontalReflectionConfiguration n c).continuous.measurable
  let stripReflectedProbability : IsProbabilityMeasure
      (μ.map (stripHorizontalReflectionConfiguration n c)) :=
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
  change (μ.map (stripHorizontalReflectionConfiguration n c)) E = μ E
  rw [Measure.map_apply hm hE.isOpen.measurableSet]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (strip_limit_clopen_reflection_eq θ n c μ hμ E hE hup).symm

/-- The self-dual strip measure has the whole-law reflection identity needed
by the original source case split and unequal arm seeds. -/
theorem selfDualStripMeasure_horizontalReflection_invariant
    (q : Set.Ici (1 : ℝ)) (n : ℕ) (c : ℤ) :
    (selfDualStripMeasure q n).map (stripHorizontalReflectionConfiguration n c) =
      selfDualStripMeasure q n :=
  strip_limit_horizontalReflection_invariant (selfDualParameters q) n c _
    (selfDualStripMeasure_isLimit q n)

end
end PottsContinuity.RSW
