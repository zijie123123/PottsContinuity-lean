module

public import PottsContinuity.Thm3.Prop4.RawLowerFrontierFit
public import PottsContinuity.Thm3.Prop4.RawPhysicalBoundary

/-! # Finite cell realization of the actual marked lower raw frontier -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.FK.Medial
noncomputable section

/-- A finite cell presentation of a sampled face region, with its two unused
bottom corner cells filled. These cells touch no sampled original bond. -/
def markedLowerFaceCells (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop) : Finset LatticeVertex := by
  classical
  exact insert (a.1-1,a.2-1) (insert (a.1+(w : ℤ),a.2-1)
    ((PD.FK.latticeRectangle (a.1-1,a.2-1) (w+1) (h+1)).filter fun f =>
      ((a.1 ≤ f.1 ∧ f.1 < a.1+(w : ℤ)) ∨ (a.2 ≤ f.2 ∧ f.2 < a.2+(h : ℤ))) ∧ P f))

/-- Literal membership of the finite presentation, including both added corners. -/
theorem mem_markedLowerFaceCells (a : LatticeVertex) (w h : ℕ) (P : LatticeVertex → Prop)
    (f : LatticeVertex) :
    f ∈ markedLowerFaceCells a w h P ↔
      f = (a.1-1,a.2-1) ∨ f = (a.1+(w : ℤ),a.2-1) ∨
      (a.1-1 ≤ f.1 ∧ f.1 ≤ a.1+(w : ℤ)) ∧ (a.2-1 ≤ f.2 ∧ f.2 ≤ a.2+(h : ℤ)) ∧
      ((a.1 ≤ f.1 ∧ f.1 < a.1+(w : ℤ)) ∨ (a.2 ≤ f.2 ∧ f.2 < a.2+(h : ℤ))) ∧ P f := by
  classical
  simp only [markedLowerFaceCells,Finset.mem_insert,Finset.mem_filter,PD.FK.mem_latticeRectangle]
  push_cast
  constructor <;> intro hf <;> rcases hf with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right; rcases h with ⟨⟨hx,hy⟩,hP⟩; exact ⟨by simpa using hx,by simpa using hy,hP⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right; rcases h with ⟨hx,hy,hP⟩; exact ⟨⟨by simpa using hx,by simpa using hy⟩,hP⟩

/-- Every genuine sampled bond face has its original region label, unchanged
by the finite presentation and the two unused corner cells. -/
theorem markedLowerFaceCells_bond_face_iff (a : LatticeVertex) (w h : ℕ)
    (P : LatticeVertex → Prop) (b : LatticeBond)
    (hb : b.source ∈ PD.FK.latticeRectangle a w h ∧ b.target ∈ PD.FK.latticeRectangle a w h)
    (side : Bool) : b.faceBase side ∈ markedLowerFaceCells a w h P ↔ P (b.faceBase side) := by
  have hs := (PD.FK.mem_latticeRectangle a b.source w h).mp hb.1
  have ht := (PD.FK.mem_latticeRectangle a b.target w h).mp hb.2
  have hgeom :
      (a.1-1 ≤ (b.faceBase side).1 ∧ (b.faceBase side).1 ≤ a.1+(w : ℤ)) ∧
      (a.2-1 ≤ (b.faceBase side).2 ∧ (b.faceBase side).2 ≤ a.2+(h : ℤ)) ∧
      ((a.1 ≤ (b.faceBase side).1 ∧ (b.faceBase side).1 < a.1+(w : ℤ)) ∨
        (a.2 ≤ (b.faceBase side).2 ∧ (b.faceBase side).2 < a.2+(h : ℤ))) ∧
      b.faceBase side ≠ (a.1-1,a.2-1) ∧ b.faceBase side ≠ (a.1+(w : ℤ),a.2-1) := by
    rcases b with ⟨⟨x,y⟩,axis⟩
    cases axis <;> cases side <;>
      dsimp [LatticeBond.source,LatticeBond.target,LatticeBond.faceBase] at hs ht ⊢ <;>
      simp only [Prod.mk.injEq] <;> omega
  rw [mem_markedLowerFaceCells]
  tauto

end
end PottsContinuity.Thm3.Prop4
