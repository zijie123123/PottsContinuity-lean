module

public import PottsContinuity.Thm3.Push.StripSourceCylinder
public import PottsContinuity.Thm3.Push.StripTranslationProbability

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory Topology
noncomputable section

/-- Reading a translated strip state on a source square is the same as
reading the original state on the translated original source bonds. -/
theorem stripSourceSquareRestriction_translation (n : ℕ) (x a : ℤ)
    (ω : RSW.StripConfiguration n) :
    stripSourceSquareRestriction n x (stripTranslation n a ω) =
      stripSourceSquareRestriction n (x+a) ω := by
  ext e
  rw [mem_stripSourceSquareRestriction,mem_stripSourceSquareRestriction]
  change ω ((stripTranslationIso n a).mapEdgeSet
    ((intervalArmStripGraphEmbedding n x).mapEdgeSet e)) = true ↔ _
  have hedge : (stripTranslationIso n a).mapEdgeSet
      ((intervalArmStripGraphEmbedding n x).mapEdgeSet e) =
      (intervalArmStripGraphEmbedding n (x+a)).mapEdgeSet e := by
    apply Subtype.ext
    change Sym2.map (stripTranslationIso n a)
      (Sym2.map (intervalArmStripGraphEmbedding n x) e.val) =
      Sym2.map (intervalArmStripGraphEmbedding n (x+a)) e.val
    rw [Sym2.map_map]
    have hf : (stripTranslationIso n a) ∘ (intervalArmStripGraphEmbedding n x) =
        (intervalArmStripGraphEmbedding n (x+a)) := by
      funext u
      apply Subtype.ext
      change (x+u.val.1+a,u.val.2) = (x+a+u.val.1,u.val.2)
      congr 1
      omega
    rw [hf]
  rw [hedge]

/-- The exact source-cylinder event commutes with translation. -/
theorem stripSourceSquareEvent_preimage_translation (n : ℕ) (x a : ℤ)
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) :
    (stripTranslation n a) ⁻¹' (stripSourceSquareEvent n x E) =
      stripSourceSquareEvent n (x+a) E := by
  ext ω
  change stripSourceSquareRestriction n x (stripTranslation n a ω) ∈ E ↔ _
  rw [stripSourceSquareRestriction_translation]
  rfl

/-- The original source bond restriction preserves the state order. -/
theorem stripSourceSquareRestriction_monotone (n : ℕ) (x : ℤ) :
    Monotone (stripSourceSquareRestriction n x) := by
  intro ω η h e he
  rw [mem_stripSourceSquareRestriction] at he ⊢
  exact Bool.le_iff_imp.mp (h _) he

/-- Every increasing source event remains increasing as its literal cylinder. -/
theorem stripSourceSquareEvent_isUpperSet (n : ℕ) (x : ℤ)
    (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n)))) (hE : IsUpperSet E) :
    IsUpperSet (stripSourceSquareEvent n x E) := by
  intro ω η h hω
  exact hE (stripSourceSquareRestriction_monotone n x h) hω

/-- All translated placements of any increasing finite source event have
identical probabilities under the actual top-only strip limit. -/
theorem strip_limit_sourceSquareEvent_translation (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x a : ℤ) (E : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n))))
    (hE : IsUpperSet E) :
    μ.real (stripSourceSquareEvent n x E) = μ.real (stripSourceSquareEvent n (x+a) E) := by
  rw [← stripSourceSquareEvent_preimage_translation]
  exact strip_limit_clopen_translation θ n μ hμ a _
    (stripSourceSquareEvent_isClopen n x E) (stripSourceSquareEvent_isUpperSet n x E hE)

end
end PottsContinuity.Push
