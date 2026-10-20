module

public import PottsContinuity.Thm3.RSW.Lemma4SideResidual
public import PottsContinuity.Thm3.RSW.InducedConfiguration

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The full original induced side rectangle, before observing its base bonds. -/
abbrev lemma4SideFullGraph (n : ℕ) (σ : ℤ) :=
  (lemma4AmbientGraph n).induce (lemma4SideVertices n σ)

/-- The original middle reveal restricted to the full side carrier. -/
def lemma4SideBaseReveal (n : ℕ) (σ : ℤ) :
    Configuration (lemma4SideFullGraph n σ) :=
  inducedConfigurationRestriction (lemma4SideVertices n σ) (lemma4MiddleReveal n)

/-- A removed side bond has both endpoints on its wired base row. -/
theorem lemma4SideBaseReveal_endpoints (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) {e : (lemma4SideFullGraph n σ).edgeSet}
    (he : e ∈ lemma4SideBaseReveal n σ) {v : lemma4SideVertices n σ}
    (hv : v ∈ e.val) : v ∈ lemma4SideBase n σ := by
  have he' : embeddedEdgeEmbedding (lemma4SideFullGraph n σ) (lemma4AmbientGraph n)
      (inducedVertexEmbedding (lemma4SideVertices n σ))
      (inducedVertexEmbedding_map_le (lemma4SideVertices n σ)) e ∈ lemma4MiddleReveal n :=
    (mem_embeddedConfigurationRestriction _ _ _ _ _ e).mp he
  have hm := lemma4MiddleReveal_endpoint n he' (by
    rw [embeddedEdgeEmbedding_coe]
    exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩)
  change |v.val.val.2| ≤ 2*(n:ℤ) at hm
  have hs : 2*(n:ℤ) ≤ σ*v.val.val.2 := v.property
  change σ*v.val.val.2 = 2*(n:ℤ)
  rw [abs_le] at hm
  rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] at * <;> omega

/-- Every removed side edge is already identified by the reference boundary. -/
theorem lemma4SideBaseReveal_prewired (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1)
    (u v : lemma4SideVertices n σ) (huv : (lemma4SideFullGraph n σ).Adj u v)
    (he : (⟨s(u,v), (lemma4SideFullGraph n σ).mem_edgeSet.mpr huv⟩ :
      (lemma4SideFullGraph n σ).edgeSet) ∈ lemma4SideBaseReveal n σ) :
    (BoundaryCondition.wired (lemma4SideBase n σ)).partition.r u v := by
  apply (BoundaryCondition.wired_rel _ _ _).mpr
  exact Or.inr ⟨lemma4SideBaseReveal_endpoints n σ hσ he (by simp),
    lemma4SideBaseReveal_endpoints n σ hσ he (by simp)⟩

end
end PottsContinuity.RSW
