module

public import PottsContinuity.Thm3.Push.StripTranslationGeometry

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- The closed extension of a translated-window restriction is bounded by
the translated full host state, on every original strip bond. -/
theorem stripWindow_translation_restriction_le (n m M : ℕ) (a : ℤ)
    (hfit : |a|+(m:ℤ) ≤ (M:ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce
      (RSW.stripWindow n M : Set (ℤ × ℤ)))) :
    RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m
      (embeddedConfigurationRestriction _ _ (stripWindowTranslationEmbedding n m M a hfit)
        (stripWindowTranslation_map_le n m M a hfit) C)) ≤
    stripTranslation n a (RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n M C)) := by
  classical
  intro e
  apply Bool.le_iff_imp.mpr
  intro he
  simp only [RSW.stripPlaneRestriction,RSW.stripWindowPlaneConfiguration,
    decide_eq_true_eq] at he
  obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp he
  let fH := embeddedEdgeEmbedding _ _ (stripWindowTranslationEmbedding n m M a hfit)
    (stripWindowTranslation_map_le n m M a hfit) f
  have hC : fH ∈ C := (mem_embeddedConfigurationRestriction _ _ _ _ C f).mp hf
  have hedge : (RSW.stripWindowPlaneEmbedding n M).mapEdgeSet fH =
      (RSW.stripPlaneEmbedding n).mapEdgeSet ((stripTranslationIso n a).mapEdgeSet e) := by
    apply Subtype.ext
    have hv := congrArg (fun z => Sym2.map (fun w : ℤ × ℤ => (w.1+a,w.2)) z.val) hfe
    change Sym2.map Subtype.val
      (Sym2.map (stripWindowTranslationEmbedding n m M a hfit) f.val) =
      Sym2.map Subtype.val (Sym2.map (stripTranslationIso n a) e.val)
    rw [Sym2.map_map,Sym2.map_map]
    change Sym2.map (fun w => (w.val.1+a,w.val.2)) f.val =
      Sym2.map (fun w => (w.val.1+a,w.val.2)) e.val
    change Sym2.map (fun w : ℤ × ℤ => (w.1+a,w.2)) (Sym2.map Subtype.val f.val) =
      Sym2.map (fun w : ℤ × ℤ => (w.1+a,w.2)) (Sym2.map Subtype.val e.val) at hv
    simpa only [Sym2.map_map,Function.comp_def] using hv
  simp only [stripTranslation,RSW.stripPlaneRestriction,RSW.stripWindowPlaneConfiguration,
    decide_eq_true_eq]
  rw [← hedge]
  exact Finset.mem_map.mpr ⟨fH,hC,rfl⟩

end
end PottsContinuity.Push
