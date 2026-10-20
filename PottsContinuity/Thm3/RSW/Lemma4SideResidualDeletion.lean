module

public import PottsContinuity.Thm3.RSW.Lemma4SideBaseDeletion

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Deleting the observed base bonds from the full side is exactly the
original residual side graph, on the complete original side vertex carrier. -/
theorem lemma4SideResidualGraph_eq_delete_base (n : ℕ) (σ : ℤ) :
    lemma4SideResidualGraph n σ =
      edgeRestriction (lemma4SideFullGraph n σ) (lemma4SideBaseReveal n σ) := by
  classical
  ext u v
  simp only [lemma4SideResidualGraph, SimpleGraph.induce_adj, edgeRestriction,
    SimpleGraph.deleteEdges_adj]
  change ((lemma4AmbientGraph n).Adj u.val v.val ∧
    s(u.val,v.val) ∉ openEdges (lemma4AmbientGraph n) (lemma4MiddleReveal n)) ↔
    ((lemma4SideFullGraph n σ).Adj u v ∧
      s(u,v) ∉ openEdges (lemma4SideFullGraph n σ) (lemma4SideBaseReveal n σ))
  by_cases huv : (lemma4SideFullGraph n σ).Adj u v
  · have he : (⟨s(u,v), (lemma4SideFullGraph n σ).mem_edgeSet.mpr huv⟩ :
        (lemma4SideFullGraph n σ).edgeSet) ∈ lemma4SideBaseReveal n σ ↔
      (⟨s(u.val,v.val), (lemma4AmbientGraph n).mem_edgeSet.mpr huv⟩ :
        (lemma4AmbientGraph n).edgeSet) ∈ lemma4MiddleReveal n := by
      exact mem_embeddedConfigurationRestriction _ _ _ _ _ _
    rw [← coe_mem_openEdges_iff] at he
    have he' := (coe_mem_openEdges_iff (lemma4AmbientGraph n) (lemma4MiddleReveal n)
      ⟨s(u.val,v.val), (lemma4AmbientGraph n).mem_edgeSet.mpr huv⟩)
    exact and_congr Iff.rfl (not_congr (he'.trans he.symm))
  · exact iff_of_false (fun h => huv h.1) (fun h => huv h.1)

end
end PottsContinuity.RSW
