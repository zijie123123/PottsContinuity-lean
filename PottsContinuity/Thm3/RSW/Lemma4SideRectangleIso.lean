module

public import PottsContinuity.Thm3.RSW.Lemma4SideBaseDeletion
public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Reflect the lower side upwards and translate its base to height zero.
Both original side carriers become the same full 112n by 54n rectangle. -/
def lemma4SideRectangleVertexEquiv (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) :
    lemma4SideVertices n σ ≃ RectangleVertex (-56*(n:ℤ),0) (112*n) (54*n) where
  toFun v := ⟨(v.val.val.1, σ*v.val.val.2 - 2*(n:ℤ)), by
    have hb := (Foundations.mem_box_iff_interval (56*n) v.val.val).mp v.val.property
    have hs : 2*(n:ℤ) ≤ σ*v.val.val.2 := v.property
    rw [mem_latticeRectangle]
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hb ⊢
    rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] at * <;> omega⟩
  invFun v := ⟨⟨(v.val.1,σ*(v.val.2+2*(n:ℤ))), by
    have hb := (mem_latticeRectangle _ _ _ _).mp v.property
    rw [Foundations.mem_box_iff_interval]
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hb ⊢
    rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] at * <;> omega⟩, by
    have hb := (mem_latticeRectangle _ _ _ _).mp v.property
    change 2*(n:ℤ) ≤ σ*(σ*(v.val.2+2*(n:ℤ)))
    rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul,neg_neg] <;> omega⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change σ*(σ*v.val.val.2-2*(n:ℤ)+2*(n:ℤ)) = v.val.val.2
    rcases hσ with rfl | rfl <;> simp
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    change σ*(σ*(v.val.2+2*(n:ℤ)))-2*(n:ℤ) = v.val.2
    rcases hσ with rfl | rfl <;> simp

/-- The coordinate map is an actual graph isomorphism, before any wiring or
edge deletion. It preserves all original vertices and nearest-neighbour bonds. -/
def lemma4SideFullRectangleIso (n : ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    lemma4SideFullGraph n σ ≃g rectangleGraph (-56*(n:ℤ),0) (112*n) (54*n) where
  toEquiv := lemma4SideRectangleVertexEquiv n σ hσ
  map_rel_iff' := by
    intro u v
    change PD.FK.squareLattice.Adj (u.val.val.1,σ*u.val.val.2-2*(n:ℤ))
      (v.val.val.1,σ*v.val.val.2-2*(n:ℤ)) ↔ PD.FK.squareLattice.Adj u.val.val v.val.val
    rw [squareLattice_adj_iff,squareLattice_adj_iff]
    rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] <;> omega

/-- The reference wired base is exactly the bottom side of the coordinate rectangle. -/
theorem lemma4SideFullRectangleIso_base (n : ℕ) (σ : ℤ)
    (hσ : σ = 1 ∨ σ = -1) (v : lemma4SideVertices n σ) :
    v ∈ lemma4SideBase n σ ↔ (lemma4SideFullRectangleIso n σ hσ v).val.2 = 0 := by
  change σ*v.val.val.2 = 2*(n:ℤ) ↔ σ*v.val.val.2-2*(n:ℤ) = 0
  omega

end
end PottsContinuity.RSW
