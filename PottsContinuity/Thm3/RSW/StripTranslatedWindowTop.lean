module

public import PottsContinuity.Thm3.RSW.StripMonotone
public import PottsContinuity.Thm3.RSW.TranslatedAnnulus

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

-- Comparison route from FKC.FiniteFK.HorizontalStripTranslationInvariance;
-- original PD parameters allow independent interior p and every real q>=1.
theorem stripWindow_translation_containment (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    ∀ z ∈ stripWindow n M, (z.1+c,z.2+0) ∈ stripWindow n N := by
  intro z hz
  have hMN' : (M:ℤ)+(c.natAbs:ℤ) ≤ N := by exact_mod_cast hMN
  have hpos : c ≤ (c.natAbs:ℤ) := Int.le_natAbs
  have hneg : -(c.natAbs:ℤ) ≤ c := by
    have h : -c ≤ ((-c).natAbs:ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h
    omega
  simp only [stripWindow,PottsContinuity.latticeRectangle,
    Finset.mem_product,Finset.mem_Icc,add_zero] at hz ⊢
  exact ⟨⟨by omega,by omega⟩,hz.2⟩

theorem stripWindow_translated_top_pullback_partition (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) :
    (isolatedExtensionPullbackBoundary
      (translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
        (stripWindow_translation_containment n M N c hMN))
      (stripWindowBoundary n N 0)).partition = (stripWindowBoundary n M 0).partition := by
  let f := translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
    (stripWindow_translation_containment n M N c hMN)
  apply Setoid.ext
  intro u v
  change ((f u = f v) ∨ f u ∈ stripWindowWiredVertices n N 0 ∧
      f v ∈ stripWindowWiredVertices n N 0) ↔
    ((u = v) ∨ u ∈ stripWindowWiredVertices n M 0 ∧ v ∈ stripWindowWiredVertices n M 0)
  simp only [stripWindowWiredVertices,Set.mem_ofPred_eq,Fin.zero_ne_one,false_and,or_false]
  change (f u = f v ∨ (u.val.2+0 = 3*(n:ℤ) ∧ v.val.2+0 = 3*(n:ℤ))) ↔
    (u = v ∨ (u.val.2 = 3*(n:ℤ) ∧ v.val.2 = 3*(n:ℤ)))
  simp only [add_zero]
  exact or_congr f.injective.eq_iff Iff.rfl

theorem stripWindow_translated_probability_le (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N) (θ : Parameters)
    (E : Set (Configuration (PottsContinuity.squareLattice.induce
      (stripWindow n M : Set (ℤ × ℤ))))) (hE : IsUpperSet E) :
    (measure (PottsContinuity.squareLattice.induce (stripWindow n M : Set (ℤ × ℤ)))
      θ (stripWindowBoundary n M 0) E).toReal ≤
    (measure (PottsContinuity.squareLattice.induce (stripWindow n N : Set (ℤ × ℤ)))
      θ (stripWindowBoundary n N 0) {C | embeddedConfigurationRestriction _ _
        (translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
          (stripWindow_translation_containment n M N c hMN))
        (translatedWindow_graph_le (stripWindow n M) (stripWindow n N) (c,0)
          (stripWindow_translation_containment n M N c hMN)) C ∈ E}).toReal := by
  let f := translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
    (stripWindow_translation_containment n M N c hMN)
  have hp := embedded_boundary_probability_le _ _ f
    (translatedWindow_graph_le _ _ (c,0) (stripWindow_translation_containment n M N c hMN))
    θ (stripWindowBoundary n N 0) E hE
  have hpart := stripWindow_translated_top_pullback_partition n M N c hMN
  have heq : measure (PottsContinuity.squareLattice.induce
      (stripWindow n M : Set (ℤ × ℤ))) θ
      (isolatedExtensionPullbackBoundary f (stripWindowBoundary n N 0)) =
      measure (PottsContinuity.squareLattice.induce
        (stripWindow n M : Set (ℤ × ℤ))) θ (stripWindowBoundary n M 0) := by
    unfold PD.FK.measure
    rw [law_eq_of_boundary_partition_eq θ _ _ hpart]
  rw [heq] at hp
  exact hp

end
end PottsContinuity.RSW
