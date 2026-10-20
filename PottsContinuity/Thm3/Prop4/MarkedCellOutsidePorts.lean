module

public import PottsContinuity.Thm3.Push.CellBoundaryMixedIncidence
public import PottsContinuity.Thm3.Push.FilledFaceBoundaryRows
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Exterior neighbors of a cell frontier cut at two prescribed marks -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push
noncomputable section

/-- Literal exterior neighbors of a cell frontier with two marked side
jumps. The bottom corners are filled to keep the outer bottom labels equal. -/
theorem cellBoundary_outside_neighbor_iff_of_marked_side_labels
    (a : LatticeVertex) (w h : ℕ) (S : Finset LatticeVertex)
    (u v z : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (hleft : ∀ y : ℤ, a.2-1 ≤ y → y ≤ a.2+(h : ℤ) →
      ((a.1-1,y) ∈ S ↔ y < u.val.2))
    (hright : ∀ y : ℤ, a.2-1 ≤ y → y ≤ a.2+(h : ℤ) →
      ((a.1+(w : ℤ),y) ∈ S ↔ y < v.val.2))
    (hbottom : ∀ x : ℤ, a.1-1 ≤ x → x ≤ a.1+(w : ℤ) → (x,a.2-1) ∈ S)
    (htop : ∀ x : ℤ, a.1-1 ≤ x → x ≤ a.1+(w : ℤ) → (x,a.2+(h : ℤ)) ∉ S)
    (t : LatticeVertex) :
    ((latticeCellBoundaryGraph S).Adj z.val t ∧ t ∉ PD.FK.latticeRectangle a w h) ↔
      (z = u ∧ t = (a.1-1,u.val.2)) ∨
      (z = v ∧ t = (a.1+(w : ℤ)+1,v.val.2)) := by
  have hz := (PD.FK.mem_latticeRectangle a z.val w h).mp z.property
  have hub := (PD.FK.mem_latticeRectangle a u.val w h).mp u.property
  have hvb := (PD.FK.mem_latticeRectangle a v.val w h).mp v.property
  constructor
  · rintro ⟨hzt,ht⟩
    have hadj := (squareLattice_adj_iff z.val t).mp (latticeCellBoundaryGraph_le S hzt)
    have ht' := ht
    rw [PD.FK.mem_latticeRectangle] at ht'
    rcases hadj with ⟨hxr | hxl,hyy⟩ | ⟨hxx,hyu | hyd⟩
    · have hx : z.val.1 = a.1+(w : ℤ) ∧ t.1 = a.1+(w : ℤ)+1 := by omega
      have hstep : (latticeCellBoundaryGraph S).Adj (a.1+(w : ℤ),z.val.2)
          (a.1+(w : ℤ)+1,z.val.2) := by
        convert hzt using 1 <;> apply Prod.ext <;> dsimp <;> omega
      have hcut := (cellBoundary_adj_right_iff S (a.1+(w : ℤ)) z.val.2).mp hstep
      have h₀ := hright z.val.2 (by omega) (by omega)
      have h₁ := hright (z.val.2-1) (by omega) (by omega)
      have heq : z.val.2 = v.val.2 := by
        by_contra hn
        apply hcut
        apply propext
        exact h₀.trans ((by omega : z.val.2 < v.val.2 ↔ z.val.2-1 < v.val.2).trans h₁.symm)
      right
      exact ⟨Subtype.ext (Prod.ext (by omega) heq),Prod.ext hx.2 (by omega)⟩
    · have hx : z.val.1 = a.1 ∧ t.1 = a.1-1 := by omega
      have hstep : (latticeCellBoundaryGraph S).Adj (a.1-1,z.val.2) ((a.1-1)+1,z.val.2) := by
        convert hzt.symm using 1 <;> apply Prod.ext <;> dsimp <;> omega
      have hcut := (cellBoundary_adj_right_iff S (a.1-1) z.val.2).mp hstep
      have h₀ := hleft z.val.2 (by omega) (by omega)
      have h₁ := hleft (z.val.2-1) (by omega) (by omega)
      have heq : z.val.2 = u.val.2 := by
        by_contra hn
        apply hcut
        apply propext
        exact h₀.trans ((by omega : z.val.2 < u.val.2 ↔ z.val.2-1 < u.val.2).trans h₁.symm)
      left
      exact ⟨Subtype.ext (Prod.ext (by omega) heq),Prod.ext hx.2 (by omega)⟩
    · have hy : z.val.2 = a.2+(h : ℤ) ∧ t.2 = a.2+(h : ℤ)+1 := by omega
      have hstep : (latticeCellBoundaryGraph S).Adj (z.val.1,a.2+(h : ℤ))
          (z.val.1,a.2+(h : ℤ)+1) := by
        convert hzt using 1 <;> apply Prod.ext <;> dsimp <;> omega
      have hcut := (cellBoundary_adj_up_iff S z.val.1 (a.2+(h : ℤ))).mp hstep
      exact (hcut (propext (iff_of_false (htop _ (by omega) (by omega))
        (htop _ (by omega) (by omega))))).elim
    · have hy : z.val.2 = a.2 ∧ t.2 = a.2-1 := by omega
      have hstep : (latticeCellBoundaryGraph S).Adj (z.val.1,a.2-1) (z.val.1,(a.2-1)+1) := by
        convert hzt.symm using 1 <;> apply Prod.ext <;> dsimp <;> omega
      have hcut := (cellBoundary_adj_up_iff S z.val.1 (a.2-1)).mp hstep
      exact (hcut (propext (iff_of_true (hbottom _ (by omega) (by omega))
        (hbottom _ (by omega) (by omega))))).elim
  · rintro (⟨hzu,ht⟩ | ⟨hzv,ht⟩)
    · subst z
      subst t
      constructor
      · have hstep : (latticeCellBoundaryGraph S).Adj (a.1-1,u.val.2) ((a.1-1)+1,u.val.2) := by
          apply (cellBoundary_adj_right_iff S _ _).mpr
          intro heq
          have h₀ := hleft u.val.2 (by omega) (by omega)
          have h₁ := hleft (u.val.2-1) (by omega) (by omega)
          have hbad := h₀.mp ((Iff.of_eq heq).mpr (h₁.mpr (by omega)))
          omega
        convert hstep.symm using 1; apply Prod.ext <;> dsimp; omega
      · rw [PD.FK.mem_latticeRectangle]
        omega
    · subst z
      subst t
      constructor
      · have hstep : (latticeCellBoundaryGraph S).Adj (a.1+(w : ℤ),v.val.2)
            (a.1+(w : ℤ)+1,v.val.2) := by
          apply (cellBoundary_adj_right_iff S _ _).mpr
          intro heq
          have h₀ := hright v.val.2 (by omega) (by omega)
          have h₁ := hright (v.val.2-1) (by omega) (by omega)
          have hbad := h₀.mp ((Iff.of_eq heq).mpr (h₁.mpr (by omega)))
          omega
        convert hstep using 1; apply Prod.ext <;> dsimp; omega
      · rw [PD.FK.mem_latticeRectangle]
        omega

end
end PottsContinuity.Thm3.Prop4
