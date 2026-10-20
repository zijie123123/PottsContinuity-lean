module

public import PottsContinuity.Thm3.Push.PushShiftGeometry
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- Exact original bond-state transport under the divisible-scale shift. -/
theorem pushShiftRestriction_edge_state (k ℓ : ℝ) (s : ℕ)
    (A : Configuration (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (ℓ+1/3) (3*s) : Set LatticeVertex)))
    (e : (PottsContinuity.squareLattice.induce
      (topWiredRectangle k ℓ (3*s) : Set LatticeVertex)).edgeSet) :
    (boolConfigurationEquiv _).symm
      (embeddedConfigurationRestriction _ _ (pushShiftEmbedding k ℓ s).toEmbedding
        (pushShiftEmbedding_map_le k ℓ s) A) e =
    (boolConfigurationEquiv _).symm A ((pushShiftEmbedding k ℓ s).mapEdgeSet e) := by
  rw [bool_embeddedRestriction_state]
  rfl

/-- Actual open graph embedding for the shifted restricted original states. -/
def pushShiftRestrictedOpenEmbedding (k ℓ : ℝ) (s : ℕ)
    (A : Configuration (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (ℓ+1/3) (3*s) : Set LatticeVertex))) :
    rcOpenGraph (topWiredRectangle k ℓ (3*s))
      ((boolConfigurationEquiv _).symm (embeddedConfigurationRestriction _ _
        (pushShiftEmbedding k ℓ s).toEmbedding (pushShiftEmbedding_map_le k ℓ s) A)) ↪g
    rcOpenGraph (topWiredRectangle k (ℓ+1/3) (3*s)) ((boolConfigurationEquiv _).symm A) where
  toFun := pushShiftEmbedding k ℓ s
  inj' := (pushShiftEmbedding k ℓ s).injective
  map_rel_iff' := by
    intro u v
    let ω := (boolConfigurationEquiv _).symm (embeddedConfigurationRestriction _ _
      (pushShiftEmbedding k ℓ s).toEmbedding (pushShiftEmbedding_map_le k ℓ s) A)
    let j := openStateEmbedding (pushShiftEmbedding k ℓ s) ω
      ((boolConfigurationEquiv _).symm A) (pushShiftRestriction_edge_state k ℓ s A)
    have hj := j.map_rel_iff' (a := u) (b := v)
    change (rcOpenGraph (topWiredRectangle k (ℓ+1/3) (3*s))
      ((boolConfigurationEquiv _).symm A)).Adj (pushShiftEmbedding k ℓ s u) (pushShiftEmbedding k ℓ s v) ↔
      (openGraph _ (boolConfigurationEquiv _ ω)).Adj u v at hj
    erw [rcOpenGraph_eq] at hj
    exact hj

/-- The shifted original bottom crossing lies in the exact upper band
[s,4*s]. Every path vertex is transported, not just its endpoints. -/
theorem shifted_restricted_crossing_implies_upper_band (k ℓ : ℝ) (s : ℕ)
    (A : Configuration (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (ℓ+1/3) (3*s) : Set LatticeVertex)))
    (hcross : horizontalCrossing (topWiredRectangle k ℓ (3*s))
      (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ)
      ((boolConfigurationEquiv _).symm (embeddedConfigurationRestriction _ _
        (pushShiftEmbedding k ℓ s).toEmbedding (pushShiftEmbedding_map_le k ℓ s) A))) :
    horizontalCrossing (topWiredRectangle k (ℓ+1/3) (3*s))
      (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ s (4*s : ℕ) ((boolConfigurationEquiv _).symm A) := by
  obtain ⟨x,y,p,hx,hy,hp⟩ := hcross
  let j := pushShiftRestrictedOpenEmbedding k ℓ s A
  refine ⟨j x,j y,p.map j.toHom,?_,?_,?_⟩
  · change (x.val.1,x.val.2+(s : ℤ)) ∈ ({-⌊k*(3*s : ℕ)⌋} : Set ℤ) ×ˢ Set.Icc (s : ℤ) (4*s : ℕ)
    simp only [Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc] at hx ⊢
    push_cast at hx ⊢
    exact ⟨hx.1,by omega,by omega⟩
  · change (y.val.1,y.val.2+(s : ℤ)) ∈ ({⌊k*(3*s : ℕ)⌋} : Set ℤ) ×ˢ Set.Icc (s : ℤ) (4*s : ℕ)
    simp only [Set.mem_prod,Set.mem_singleton_iff,Set.mem_Icc] at hy ⊢
    push_cast at hy ⊢
    exact ⟨hy.1,by omega,by omega⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    have hvp := hp v hv
    change (v.val.1,v.val.2+(s : ℤ)) ∈ Set.Icc (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ ×ˢ
      Set.Icc (s : ℤ) (4*s : ℕ)
    simp only [Set.mem_prod,Set.mem_Icc] at hvp ⊢
    push_cast at hvp ⊢
    exact ⟨hvp.1,by omega,by omega⟩

end
end PottsContinuity.Push
