module

public import PottsContinuity.Thm3.RSW.StripTranslatedWindowTop
public import PottsContinuity.Thm3.RSW.StripHorizontalTranslation
public import PottsContinuity.Thm3.RSW.StripEventLimit

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The translated sample reads the inverse-translated original edge. -/
theorem stripHorizontalTranslationConfiguration_apply (n : ℕ) (c : ℤ)
    (ω : StripConfiguration n) (e : (stripGraph n).edgeSet) :
    stripHorizontalTranslationConfiguration n c ω e =
      ω ((stripHorizontalTranslationIso n (-c)).mapEdgeSet e) := by
  have h := stripHorizontalTranslationConfiguration_edge n c ω
    ((stripHorizontalTranslationIso n (-c)).mapEdgeSet e)
  have he : (stripHorizontalTranslationIso n c).mapEdgeSet
      ((stripHorizontalTranslationIso n (-c)).mapEdgeSet e) = e := by
    simpa only [neg_neg] using stripHorizontalTranslation_edge_neg_cancel n (-c) e
  rwa [he] at h

/-- State translation preserves the original coordinatewise open-edge order. -/
theorem stripHorizontalTranslationConfiguration_monotone (n : ℕ) (c : ℤ) :
    Monotone (stripHorizontalTranslationConfiguration n c) := by
  intro ω η h e
  simp only [stripHorizontalTranslationConfiguration_apply]
  exact h _

/-- Restricting a translated inner window and closing its exterior is bounded
by inverse-translating the original larger window's actual sampled state. -/
theorem stripWindow_translated_restriction_le (n M N : ℕ) (c : ℤ)
    (hMN : M+c.natAbs ≤ N)
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow n N : Set (ℤ × ℤ)))) :
    stripPlaneRestriction n (stripWindowPlaneConfiguration n M
      (embeddedConfigurationRestriction _ _
        (translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
          (stripWindow_translation_containment n M N c hMN))
        (translatedWindow_graph_le (stripWindow n M) (stripWindow n N) (c,0)
          (stripWindow_translation_containment n M N c hMN)) C)) ≤
      stripHorizontalTranslationConfiguration n (-c)
        (stripPlaneRestriction n (stripWindowPlaneConfiguration n N C)) := by
  classical
  let f := translatedWindowVertexEmbedding (stripWindow n M) (stripWindow n N) (c,0)
    (stripWindow_translation_containment n M N c hMN)
  let hmap := translatedWindow_graph_le (stripWindow n M) (stripWindow n N) (c,0)
    (stripWindow_translation_containment n M N c hMN)
  intro e
  apply Bool.le_iff_imp.mpr
  intro h
  simp only [stripPlaneRestriction,stripWindowPlaneConfiguration,decide_eq_true_eq] at h
  obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp h
  have hC := (mem_embeddedConfigurationRestriction _ _ f hmap C g).mp hg
  rw [stripHorizontalTranslationConfiguration_apply]
  simp only [neg_neg,stripPlaneRestriction,stripWindowPlaneConfiguration,decide_eq_true_eq]
  refine Finset.mem_map.mpr ⟨embeddedEdgeEmbedding _ _ f hmap g,hC,?_⟩
  apply Subtype.ext
  change Sym2.map Subtype.val (Sym2.map f g.val) =
    Sym2.map Subtype.val (Sym2.map (stripHorizontalTranslationIso n c) e.val)
  rw [Sym2.map_map,Sym2.map_map]
  change Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => (z.val.1+c,z.val.2+0)) g.val =
    Sym2.map (fun z : stripVertices n => (z.val.1+c,z.val.2)) e.val
  have hgeval : Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => z.val) g.val =
      Sym2.map (fun z : stripVertices n => z.val) e.val := by
    exact congrArg (fun e : PottsContinuity.squareLattice.edgeSet => e.val) hge
  have htrans := congrArg (Sym2.map (fun z : ℤ × ℤ => (z.1+c,z.2))) hgeval
  simp only [Sym2.map_map] at htrans
  change Sym2.map (fun z : (stripWindow n M : Set (ℤ × ℤ)) => (z.val.1+c,z.val.2)) g.val =
    Sym2.map (fun z : stripVertices n => (z.val.1+c,z.val.2)) e.val at htrans
  simpa only [add_zero] using htrans

end
end PottsContinuity.RSW
