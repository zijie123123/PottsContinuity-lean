module

public import PottsContinuity.Thm3.RSW.Lemma4SideRectangleIso
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The transported base partition is exactly one wired class on the bottom
side, and singleton classes at every other vertex of the coordinate rectangle. -/
theorem lemma4SideRectangle_boundary_partition (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    (boundaryConditionIso (lemma4SideFullRectangleIso n σ hσ)
      (BoundaryCondition.wired (lemma4SideBase n σ))).partition =
    (BoundaryCondition.wired
      {v : RectangleVertex (-56*(n:ℤ),0) (112*n) (54*n) | v.val.2 = 0}).partition := by
  apply Setoid.ext
  intro u v
  change (BoundaryCondition.wired (lemma4SideBase n σ)).partition.r
    ((lemma4SideFullRectangleIso n σ hσ).symm u)
    ((lemma4SideFullRectangleIso n σ hσ).symm v) ↔ _
  rw [BoundaryCondition.wired_rel,BoundaryCondition.wired_rel]
  have hu := lemma4SideFullRectangleIso_base n σ hσ
    ((lemma4SideFullRectangleIso n σ hσ).symm u)
  have hv := lemma4SideFullRectangleIso_base n σ hσ
    ((lemma4SideFullRectangleIso n σ hσ).symm v)
  simp only [RelIso.apply_symm_apply] at hu hv
  rw [hu,hv]
  exact or_congr (lemma4SideFullRectangleIso n σ hσ).symm.injective.eq_iff Iff.rfl

/-- The full original side law, in explicit reflected/translated coordinates,
is precisely the rectangle FK law with its bottom side wired. -/
theorem lemma4SideFull_law_map_rectangle (θ : Parameters) (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    (law (lemma4SideFullGraph n σ) θ
      (BoundaryCondition.wired (lemma4SideBase n σ))).map
      (configurationIso (lemma4SideFullRectangleIso n σ hσ)) =
    law (rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n)) θ
      (BoundaryCondition.wired
        {v : RectangleVertex (-56*(n:ℤ),0) (112*n) (54*n) | v.val.2 = 0}) := by
  rw [law_configurationIso_map]
  exact law_eq_of_boundary_partition_eq θ _ _ (lemma4SideRectangle_boundary_partition n σ hσ)

end
end PottsContinuity.RSW
