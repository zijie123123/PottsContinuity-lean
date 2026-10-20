module

public import PottsContinuity.Thm3.Push.SourceBandEmbedding
public import PottsContinuity.Thm3.Push.EmbeddedOpenGraph
public import PottsContinuity.Thm3.Push.SourceSideArm

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section

/-- Restricting to the literal translated band is exactly the source's
confined side-arm event, with both original root coordinates retained. -/
theorem sourceBand_left_arm_iff (N a w : ℕ) (hw : a+w ≤ N) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) N N)) :
    embeddedConfigurationRestriction _ _ (sourceBandEmbedding N a w N hw le_rfl)
      (sourceBandEmbedding_map_le N a w N hw le_rfl) C ∈
        arcsConnectionEvent (rectangleGraph (0,0) w N)
          {u | u.val.2 = 0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r} {v | v.val.1 = 0} ↔
      C ∈ sourceSquareSideArmEvent N ((a:ℤ)+l) ((a:ℤ)+r) a ((a:ℤ)+w) a := by
  let f := sourceBandEmbedding N a w N hw le_rfl
  let j := embeddedRestrictionOpenEmbedding _ _ f
    (sourceBandEmbedding_map_le N a w N hw le_rfl)
    (sourceBandEmbedding_adj_iff N a w N hw le_rfl) C
  constructor
  · rintro ⟨u,hu,v,hv,⟨p⟩⟩
    refine ⟨j u,j v,p.map j.toHom,?_,?_,?_,?_,?_⟩
    · exact hu.1
    · change (a:ℤ)+l ≤ u.val.1+a
      have h := hu.2.1
      omega
    · change u.val.1+(a:ℤ) ≤ a+r
      have h := hu.2.2
      omega
    · change v.val.1 = 0 at hv
      change v.val.1+(a:ℤ) = a
      omega
    · intro z hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
      have hx := (mem_latticeRectangle (0,0) x.val w N).mp x.property
      change (a:ℤ) ≤ x.val.1+a ∧ x.val.1+a ≤ a+w
      dsimp at hx
      omega
  · rintro ⟨u₀,v₀,p,hu,hul,hur,hv,hbounds⟩
    have hsupp : ∀ z ∈ p.support, z ∈ Set.range j := by
      intro z hz
      change z ∈ Set.range f
      apply (sourceBandEmbedding_range_iff N a w N hw le_rfl z).mpr
      have hzv := (mem_latticeRectangle (0,0) z.val N N).mp z.property
      have hzb := hbounds z hz
      dsimp at hzv
      exact ⟨hzb.1,hzb.2,by omega⟩
    let u := j.isoInduceRange.symm ⟨u₀,hsupp _ p.start_mem_support⟩
    let v := j.isoInduceRange.symm ⟨v₀,hsupp _ p.end_mem_support⟩
    let q := (p.induce (Set.range j) hsupp).map j.isoInduceRange.symm.toHom
    have hfu : f u = u₀ := congrArg Subtype.val
      (j.isoInduceRange.apply_symm_apply ⟨u₀,hsupp _ p.start_mem_support⟩)
    have hfv : f v = v₀ := congrArg Subtype.val
      (j.isoInduceRange.apply_symm_apply ⟨v₀,hsupp _ p.end_mem_support⟩)
    have hux := congrArg (fun z => z.val.1) hfu
    have huy := congrArg (fun z => z.val.2) hfu
    have hvx := congrArg (fun z => z.val.1) hfv
    change u.val.1+(a:ℤ)=u₀.val.1 at hux
    change u.val.2=u₀.val.2 at huy
    change v.val.1+(a:ℤ)=v₀.val.1 at hvx
    refine ⟨u,⟨huy.trans hu,by omega,by omega⟩,v,?_,⟨q⟩⟩
    change v.val.1=0
    omega

end
end PottsContinuity.Push
