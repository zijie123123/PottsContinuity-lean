module

public import PottsContinuity.Thm3.Push.StripTranslationGeometry
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push
noncomputable section

/-- Translation carries each actual open walk to a walk of the translated
state, with the original translated vertices and bonds. -/
def stripTranslationOpenIso (n : ℕ) (a : ℤ) (ω : RSW.StripConfiguration n) :
    RSW.stripOpenGraph n (stripTranslation n a ω) ≃g RSW.stripOpenGraph n ω where
  toEquiv := (stripTranslationIso n a).toEquiv
  map_rel_iff' := by
    intro u v
    simp only [RSW.stripOpenGraph,booleanOpenGraph_adj]
    constructor
    · rintro ⟨he,ho⟩
      have hbase := (RSW.stripGraph n).mem_edgeSet.mpr
        ((stripTranslationIso n a).map_rel_iff'.mp ((RSW.stripGraph n).mem_edgeSet.mp he))
      refine ⟨hbase,?_⟩
      change ω ((stripTranslationIso n a).mapEdgeSet ⟨s(u,v),hbase⟩) = true
      have hed : (stripTranslationIso n a).mapEdgeSet ⟨s(u,v),hbase⟩ = ⟨_,he⟩ := by
        apply Subtype.ext
        rfl
      rw [hed]
      exact ho
    · rintro ⟨he,ho⟩
      have hbase := (RSW.stripGraph n).mem_edgeSet.mpr
        ((stripTranslationIso n a).map_rel_iff'.mpr ((RSW.stripGraph n).mem_edgeSet.mp he))
      refine ⟨hbase,?_⟩
      exact ho

end
end PottsContinuity.Push
