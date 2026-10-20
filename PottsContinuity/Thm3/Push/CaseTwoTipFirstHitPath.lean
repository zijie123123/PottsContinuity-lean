module

public import PottsContinuity.Thm3.Push.CaseTwoTipFirstHitSelector

@[expose] public section

namespace PottsContinuity.Push
open PD.FK
noncomputable section

/-- The selected tip record decodes to a literal original J-to-left-R' path.
Its entire confinement, retained ordered trace and first side hit are proved. -/
theorem caseTwoTipFirstHitSelector_original_path (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (record : SideCollarFirstHitRecord (5*s) (2*n))
    (hrecord : caseTwoTipFirstHitSelector n s hfit C = some record) :
    ∃ a b : RectangleVertex (0,0) (2*n) (2*n),
    ∃ q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Path a b,
      a.val.2 = 0 ∧ 6*(s:ℤ) ≤ a.val.1 ∧ a.val.1 ≤ 7*(s:ℤ) ∧ b.val.1 = 4*(s:ℤ) ∧
      q.val.support = record.2.map
        (sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl) ∧
      (∀ z ∈ q.val.support, 4*(s:ℤ) ≤ z.val.1 ∧ z.val.1 ≤ 9*(s:ℤ)) ∧
      (∀ z ∈ q.val.support, z.val.1 = 4*(s:ℤ) → z = b) := by
  classical
  let f := sourceBandEmbedding (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl
  let hGH := sourceBandEmbedding_map_le (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl
  let D := embeddedConfigurationRestriction _ _ f hGH C
  have hsmall : sideCollarFirstHitSelector (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ) D = some record := hrecord
  obtain ⟨u,hu,hul,hur,v,hv,p,_,hp,_,hfirst,_⟩ :=
    sideCollarFirstHitSelector_path_openOnFiber (5*s) (2*n) ((2*s:ℕ):ℤ) ((3*s:ℕ):ℤ)
      D D record hsmall rfl
  let j := embeddedRestrictionOpenEmbedding _ _ f hGH
    (sourceBandEmbedding_adj_iff (2*n) (4*s) (5*s) (2*n) (by omega) le_rfl) C
  let q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Path (j u) (j v) :=
    ⟨p.val.map j.toHom,p.property.map j.injective⟩
  have hq : q.val.support = p.val.support.map f := SimpleGraph.Walk.support_map _ _
  refine ⟨j u,j v,q,hu,?_,?_,?_,?_,?_,?_⟩
  · change 6*(s:ℤ) ≤ u.val.1+((4*s:ℕ):ℤ)
    push_cast at hul ⊢
    omega
  · change u.val.1+((4*s:ℕ):ℤ) ≤ 7*(s:ℤ)
    push_cast at hur ⊢
    omega
  · change v.val.1+((4*s:ℕ):ℤ) = 4*(s:ℤ)
    push_cast
    omega
  · rw [hq,hp]
  · intro z hz
    rw [hq] at hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    have hx := (mem_latticeRectangle (0,0) x.val (5*s) (2*n)).mp x.property
    change 4*(s:ℤ) ≤ x.val.1+((4*s:ℕ):ℤ) ∧ x.val.1+((4*s:ℕ):ℤ) ≤ 9*(s:ℤ)
    dsimp at hx
    push_cast at hx ⊢
    omega
  · intro z hz hzcol
    rw [hq] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    have hxcol : x.val.1=0 := by
      change x.val.1+((4*s:ℕ):ℤ) = 4*(s:ℤ) at hzcol
      push_cast at hzcol
      omega
    exact congrArg f (hfirst x hx hxcol)

end
end PottsContinuity.Push
