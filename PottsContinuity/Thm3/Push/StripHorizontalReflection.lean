module

public import PottsContinuity.Thm3.RSW.StripEventLimit
public import PottsContinuity.PD.FK.Isomorphism

@[expose] public section

namespace PottsContinuity.Push
open MeasureTheory PD.FK
noncomputable section

/-- Horizontal reflection on the actual infinite strip, fixing both boundary
rows and every vertical coordinate. -/
def stripHorizontalReflectionIso (n : ℕ) : RSW.stripGraph n ≃g RSW.stripGraph n where
  toFun w := ⟨(-w.val.1,w.val.2),w.property⟩
  invFun w := ⟨(-w.val.1,w.val.2),w.property⟩
  left_inv w := by apply Subtype.ext; simp only [neg_neg]
  right_inv w := by apply Subtype.ext; simp only [neg_neg]
  map_rel_iff' := by
    intro u v
    change |(-u.val.1)-(-v.val.1)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [neg_sub_neg,abs_sub_comm v.val.1 u.val.1]

/-- The same reflection acts on every centred finite strip window. -/
def stripWindowHorizontalReflectionIso (n m : ℕ) :
    (squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ)) where
  toFun w := ⟨(-w.val.1,w.val.2),by
    have hw := w.property
    simp only [RSW.stripWindow,latticeRectangle,Finset.mem_coe,Finset.mem_product,
      Finset.mem_Icc] at hw ⊢
    exact ⟨⟨by omega,by omega⟩,hw.2⟩⟩
  invFun w := ⟨(-w.val.1,w.val.2),by
    have hw := w.property
    simp only [RSW.stripWindow,latticeRectangle,Finset.mem_coe,Finset.mem_product,
      Finset.mem_Icc] at hw ⊢
    exact ⟨⟨by omega,by omega⟩,hw.2⟩⟩
  left_inv w := by apply Subtype.ext; simp only [neg_neg]
  right_inv w := by apply Subtype.ext; simp only [neg_neg]
  map_rel_iff' := by
    intro u v
    change |(-u.val.1)-(-v.val.1)|+|u.val.2-v.val.2|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    rw [neg_sub_neg,abs_sub_comm v.val.1 u.val.1]

/-- Reflect actual bond states by their original reflected strip edges. -/
def stripHorizontalReflection (n : ℕ) (ω : RSW.StripConfiguration n) :
    RSW.StripConfiguration n :=
  fun e => ω ((stripHorizontalReflectionIso n).mapEdgeSet e)

/-- Reflection of actual strip configurations is continuous. -/
theorem stripHorizontalReflection_continuous (n : ℕ) :
    Continuous (stripHorizontalReflection n) :=
  continuous_pi fun e => continuous_apply ((stripHorizontalReflectionIso n).mapEdgeSet e)

end
end PottsContinuity.Push
