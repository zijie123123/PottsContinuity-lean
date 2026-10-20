module

public import PottsContinuity.Thm3.RSW.StripTopRowWiring
public import PottsContinuity.PD.FK.BoxTranslation
public import PottsContinuity.PD.Duality.Rectangle

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Identity on the full physical source window identifies it with the
rectangle duality host. Every original vertex and bond is retained. -/
def stripWindowRectangleIso (n M : ℕ) :
    (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) ≃g
      rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) where
  toFun v := ⟨v.val,by
    have hv : v.val ∈ stripWindow n M := v.property
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hv
    rw [mem_latticeRectangle]
    push_cast
    constructor <;> constructor <;> omega⟩
  invFun v := ⟨v.val,by
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    change v.val ∈ stripWindow n M
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    push_cast at hv
    constructor <;> constructor <;> omega⟩
  left_inv v := rfl
  right_inv v := rfl
  map_rel_iff' := Iff.rfl

/-- The actual source top-row state induces the exact transported top
partition in the finite rectangle host, without a geometric premise. -/
theorem stripWindowRectangleIso_topRow_frozen_partition (n M : ℕ) :
    (frozenBoundary (BoundaryCondition.free ∅)
      (configurationIso (stripWindowRectangleIso n M) (stripTopRowState n M))).partition =
    (boundaryConditionIso (stripWindowRectangleIso n M) (stripWindowBoundary n M 0)).partition := by
  let e := stripWindowRectangleIso n M
  apply Setoid.ext
  intro u v
  change (componentSetoid _ (BoundaryCondition.free ∅)
      (configurationIso e (stripTopRowState n M))).r u v ↔
    (stripWindowBoundary n M 0).partition.r (e.symm u) (e.symm v)
  have h := componentSetoid_configurationIso e (BoundaryCondition.free ∅)
    (stripTopRowState n M) (e.symm u) (e.symm v)
  rw [boundaryConditionIso_free_empty] at h
  have ht : componentSetoid _ (BoundaryCondition.free ∅) (stripTopRowState n M) =
      (stripWindowBoundary n M 0).partition := stripTopRowState_frozen_partition n M
  rw [ht] at h
  simpa only [e.apply_symm_apply] using h

end
end PottsContinuity.RSW
