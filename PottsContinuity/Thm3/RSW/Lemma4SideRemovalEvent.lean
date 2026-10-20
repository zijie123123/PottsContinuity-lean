module

public import PottsContinuity.Thm3.RSW.Lemma4SidePrewiredLaw
public import PottsContinuity.Thm3.RSW.Lemma4SideReferenceEvents

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The two inclusion routes retain exactly the same original sampled bonds. -/
theorem lemma4SideRemainingEquiv_extension (n : ℕ) (σ : ℤ)
    (A : Configuration (lemma4SideResidualGraph n σ)) :
    inducedConfigurationExtension (lemma4SideVertices n σ)
      (lemma4SideRemainingEquiv n σ A).val =
    (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n)
      (inducedConfigurationExtension (lemma4SideVertices n σ) A)).val := by
  classical
  simp only [lemma4SideRemainingEquiv,Equiv.trans_apply,
    edgeRestrictionConfigurationEquiv_val, inducedConfigurationExtension,
    embeddedConfigurationEmbedding_eq_map]
  change ((A.map (configurationIsoEdgeEquiv (lemma4SideDeletionIso n σ)).toEmbedding).map
    (edgeRestrictionEdgeEmbedding _ _)).map _ = (A.map _).map _
  rw [Finset.map_map,Finset.map_map,Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro e
  apply Subtype.ext
  simp only [Function.Embedding.trans_apply,embeddedEdgeEmbedding_coe,
    edgeRestrictionEdgeEmbedding_coe]
  change Sym2.map Subtype.val (Sym2.map id e.val) = Sym2.map Subtype.val e.val
  rw [Sym2.map_id]
  rfl

/-- Restoring arbitrary observed base states leaves the actual dual band
crossing unchanged after inclusion into the original box. -/
theorem lemma4SideFull_band_restore_iff (n : ℕ) (i : Fin 2)
    (C : Configuration (lemma4SideFullGraph n (lemma4SideSign i))) :
    inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) C ∈
      lemma4DualBandEvent n i ↔
    (lemma4SideRemainingEquiv n (lemma4SideSign i)).symm
      (configurationSplitEquiv (lemma4SideFullGraph n (lemma4SideSign i))
        (lemma4SideBaseReveal n (lemma4SideSign i)) C).1 ∈ lemma4SideReferenceEvent n i := by
  classical
  let P := configurationSplitEquiv (lemma4SideFullGraph n (lemma4SideSign i))
    (lemma4SideBaseReveal n (lemma4SideSign i)) C
  have hC : P.1.val ∪ P.2.val = C :=
    (configurationSplitEquiv _ _).symm_apply_apply C
  have hK : inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) P.2.val ⊆
      lemma4MiddleReveal n := by
    apply Finset.Subset.trans
      (inducedConfigurationExtension_monotone _ P.2.property)
    exact embeddedConfigurationEmbedding_restriction_subset _ _ _ _ _
  have h := lemma4DualBandEvent_union_middle_iff n i
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) P.1.val)
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) P.2.val) hK
  have hmap : inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
      (P.1.val ∪ P.2.val) =
      inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) P.1.val ∪
      inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) P.2.val := by
    simp only [inducedConfigurationExtension,embeddedConfigurationEmbedding_eq_map,
      Finset.map_union]
  rw [← hmap,hC] at h
  have he := lemma4SideRemainingEquiv_extension n (lemma4SideSign i)
    ((lemma4SideRemainingEquiv n (lemma4SideSign i)).symm P.1)
  rw [Equiv.apply_symm_apply] at he
  change _ ↔ (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n)
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
      ((lemma4SideRemainingEquiv n (lemma4SideSign i)).symm P.1))).val ∈ lemma4DualBandEvent n i
  rw [← he]
  exact h

end
end PottsContinuity.RSW
