module

public import PottsContinuity.Thm3.RSW.StripClosedCutFailure
public import PottsContinuity.Thm3.RSW.StripWindow
public import PottsContinuity.PD.FK.BoxTranslation

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The literal vertical translation of the complete original strip window
onto the shared cut rectangle. All original vertices and edges are retained. -/
def stripWindowCutIso (n M : ℕ) :
    (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) ≃g
      FKC.Medial.horizontalStripCutRectangle M (2*n) where
  toFun v := ⟨(v.val.1,v.val.2+(n:ℤ)),by
    have hv : v.val ∈ stripWindow n M := v.property
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hv
    rw [FKC.mem_latticeRectangle]
    push_cast
    constructor <;> constructor <;> omega⟩
  invFun v := ⟨(v.val.1,v.val.2-(n:ℤ)),by
    have hv := (FKC.mem_latticeRectangle _ _ _ _).mp v.property
    change (v.val.1,v.val.2-(n:ℤ)) ∈ stripWindow n M
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    push_cast at hv
    constructor <;> constructor <;> omega⟩
  left_inv v := by apply Subtype.ext; apply Prod.ext <;> dsimp; ring
  right_inv v := by apply Subtype.ext; apply Prod.ext <;> dsimp; ring
  map_rel_iff' := by
    intro u v
    change (((u.val.1+1=v.val.1 ∨ v.val.1+1=u.val.1) ∧ u.val.2+(n:ℤ)=v.val.2+(n:ℤ)) ∨
      (u.val.1=v.val.1 ∧ (u.val.2+(n:ℤ)+1=v.val.2+(n:ℤ) ∨ v.val.2+(n:ℤ)+1=u.val.2+(n:ℤ)))) ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    constructor
    · rintro (⟨hx,hy⟩ | ⟨hx,hy⟩)
      · have hyy : u.val.2-v.val.2=0 := by omega
        have hxx : u.val.1-v.val.1=1 ∨ u.val.1-v.val.1= -1 := by omega
        rcases hxx with hxx | hxx <;> rw [hxx,hyy] <;> norm_num
      · have hxx : u.val.1-v.val.1=0 := by omega
        have hyy : u.val.2-v.val.2=1 ∨ u.val.2-v.val.2= -1 := by omega
        rcases hyy with hyy | hyy <;> rw [hxx,hyy] <;> norm_num
    · intro h
      have hx0 := abs_nonneg (u.val.1-v.val.1)
      have hy0 := abs_nonneg (u.val.2-v.val.2)
      have hxle := abs_le.mp (show |u.val.1-v.val.1| ≤ 1 by linarith only [h,hy0])
      have hyle := abs_le.mp (show |u.val.2-v.val.2| ≤ 1 by linarith only [h,hx0])
      by_cases hx : u.val.1=v.val.1
      · right
        have hyne : u.val.2 ≠ v.val.2 := by
          intro hy
          rw [hx,hy,sub_self,abs_zero] at h
          norm_num at h
        exact ⟨hx,by omega⟩
      · left
        have hxpos : 1 ≤ |u.val.1-v.val.1| := by
          have hh := abs_pos.mpr (sub_ne_zero.mpr hx)
          omega
        have hyzero : |u.val.2-v.val.2|=0 := by linarith only [h,hxpos,hy0]
        have hy : u.val.2=v.val.2 := sub_eq_zero.mp (abs_eq_zero.mp hyzero)
        exact ⟨by omega,by omega⟩

end
end PottsContinuity.RSW
