module

public import PottsContinuity.Thm3.Push.StripHorizontalReflection
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push
noncomputable section

/-- Every original strip bond is restored by two horizontal reflections. -/
theorem stripHorizontalReflection_edge_involutive (n : ℕ) :
    Function.Involutive (stripHorizontalReflectionIso n).mapEdgeSet := by
  intro e
  apply Subtype.ext
  change Sym2.map (stripHorizontalReflectionIso n)
    (Sym2.map (stripHorizontalReflectionIso n) e.val) = e.val
  rw [Sym2.map_map]
  have hfun : (fun w => stripHorizontalReflectionIso n (stripHorizontalReflectionIso n w)) = id := by
    funext w
    apply Subtype.ext
    change (-(-w.val.1),w.val.2) = w.val
    simp only [neg_neg,Prod.eta]
  change Sym2.map (fun w => stripHorizontalReflectionIso n (stripHorizontalReflectionIso n w)) e.val = e.val
  rw [hfun,Sym2.map_id]
  rfl

/-- Reflection carries each actual open walk to a walk of the reflected
state, with the original reflected vertices and bonds. -/
def stripReflectionOpenIso (n : ℕ) (ω : RSW.StripConfiguration n) :
    RSW.stripOpenGraph n (stripHorizontalReflection n ω) ≃g RSW.stripOpenGraph n ω where
  toEquiv := (stripHorizontalReflectionIso n).toEquiv
  map_rel_iff' := by
    intro u v
    simp only [RSW.stripOpenGraph,booleanOpenGraph_adj]
    constructor
    · rintro ⟨he,ho⟩
      have hbase := (RSW.stripGraph n).mem_edgeSet.mpr
        ((stripHorizontalReflectionIso n).map_rel_iff'.mp ((RSW.stripGraph n).mem_edgeSet.mp he))
      refine ⟨hbase,?_⟩
      change ω ((stripHorizontalReflectionIso n).mapEdgeSet ⟨s(u,v),hbase⟩) = true
      have hed : (stripHorizontalReflectionIso n).mapEdgeSet ⟨s(u,v),hbase⟩ = ⟨_,he⟩ := by
        apply Subtype.ext
        rfl
      rw [hed]
      exact ho
    · rintro ⟨he,ho⟩
      have hbase := (RSW.stripGraph n).mem_edgeSet.mpr
        ((stripHorizontalReflectionIso n).map_rel_iff'.mpr ((RSW.stripGraph n).mem_edgeSet.mp he))
      refine ⟨hbase,?_⟩
      exact ho

end
end PottsContinuity.Push
