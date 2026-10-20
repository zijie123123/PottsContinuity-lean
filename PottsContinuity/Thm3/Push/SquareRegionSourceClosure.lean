module

public import PottsContinuity.Thm3.Push.SquareRegionSideClosure
public import PottsContinuity.Thm3.Push.FilledFaceBoundaryRows
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- A bottom exterior cell before the source interval has the left seed label. -/
theorem squareRegionCells_bottom_before_mem (N : ℕ) (l : ℤ)
    (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (x : ℤ) (hx : -1 ≤ x) (hxN : x ≤ (N : ℤ)) (hxl : x < l) :
    (x,-1) ∈ squareRegionCells N S := by
  let v : RectangleVertex (-1,-1) (N+1) (N+1) :=
    ⟨(x,-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  exact (mem_squareRegionCells N S ((squareExpandedFaceEquiv N).symm v)).mpr
    (hleft _ ((mem_intervalArmLeftDualPorts N l _).mpr (Or.inr ⟨rfl,hxl⟩)))

/-- At/after the source interval, bottom exterior cells have the right label. -/
theorem squareRegionCells_bottom_after_not_mem (N : ℕ) (r : ℤ)
    (S : Set (RectangleDualVertex (0,0) N N))
    (hright : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S)
    (x : ℤ) (hx : -1 ≤ x) (hxN : x ≤ (N : ℤ)) (hrx : r ≤ x) :
    (x,-1) ∉ squareRegionCells N S := by
  let v : RectangleVertex (-1,-1) (N+1) (N+1) :=
    ⟨(x,-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  exact fun hm => hright _ ((mem_intervalArmRightDualPorts N r _).mpr (Or.inr ⟨rfl,hrx⟩))
    ((mem_squareRegionCells N S ((squareExpandedFaceEquiv N).symm v)).mp hm)

/-- The full cell boundary can leave the original square ONLY at the source
bottom interval or at the full top. Physical side vertices and all other
bottom vertices have every cell-boundary neighbor inside the square. -/
theorem squareRegionCell_neighbor_mem_off_source_top
    (N : ℕ) (l r : ℤ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (hright : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S)
    (u : RectangleVertex (0,0) N N) (htop : u.val.2 < (N : ℤ))
    (hbottom : u.val.2=0 → u.val.1 < l ∨ r < u.val.1)
    (v : LatticeVertex) (hxy : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val v) :
    v ∈ latticeRectangle (0,0) N N := by
  have hleftSide : ∀ b : RectangleDualVertex (0,0) N N, b.val.1 = -1 → b ∈ S := by
    intro b hb
    exact hleft b ((mem_intervalArmLeftDualPorts N l b).mpr (Or.inl hb))
  have hrightSide : ∀ b : RectangleDualVertex (0,0) N N, b.val.1 = (N : ℤ) → b ∉ S := by
    intro b hb
    exact hright b ((mem_intervalArmRightDualPorts N r b).mpr (Or.inl hb))
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have hd : |u.val.1-v.1| + |u.val.2-v.2| = 1 := latticeCellBoundaryGraph_le _ hxy
  have hdist := hd
  simp only [abs_eq_max_neg] at hdist
  have hxlo : 0 ≤ v.1 := by
    by_contra hbad
    have hxx : u.val.1 = 0 := by omega
    have hvx : v.1 = -1 := by omega
    have hyy : v.2 = u.val.2 := by omega
    have hstep : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj
        (-1,u.val.2) ((-1 : ℤ)+1,u.val.2) := by
      convert hxy.symm using 1 <;> (apply Prod.ext <;> dsimp <;> omega)
    have hcut := (cellBoundary_adj_right_iff _ (-1) u.val.2).mp hstep
    have h₁ := squareRegionCells_left_mem N S hleftSide u.val.2 (by omega) (by omega)
    have h₂ := squareRegionCells_left_mem N S hleftSide (u.val.2-1) (by omega) (by omega)
    exact hcut (propext ⟨fun _ => h₂,fun _ => h₁⟩)
  have hxhi : v.1 ≤ (N : ℤ) := by
    by_contra hbad
    have hxx : u.val.1 = (N : ℤ) := by omega
    have hvx : v.1 = (N : ℤ)+1 := by omega
    have hyy : v.2 = u.val.2 := by omega
    have hstep : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj
        ((N : ℤ),u.val.2) ((N : ℤ)+1,u.val.2) := by
      convert hxy using 1 <;> (apply Prod.ext <;> dsimp <;> omega)
    have hcut := (cellBoundary_adj_right_iff _ (N : ℤ) u.val.2).mp hstep
    have h₁ := squareRegionCells_right_not_mem N S hrightSide u.val.2 (by omega) (by omega)
    have h₂ := squareRegionCells_right_not_mem N S hrightSide (u.val.2-1) (by omega) (by omega)
    exact hcut (propext ⟨fun hm => (h₁ hm).elim,fun hm => (h₂ hm).elim⟩)
  have hylo : 0 ≤ v.2 := by
    by_contra hbad
    have hyy : u.val.2=0 := by omega
    have hxx : v.1=u.val.1 := by omega
    have hvy : v.2 = -1 := by omega
    have hstep : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj
        (u.val.1,-1) (u.val.1,(-1 : ℤ)+1) := by
      convert hxy.symm using 1 <;> (apply Prod.ext <;> dsimp <;> omega)
    have hcut := (cellBoundary_adj_up_iff _ u.val.1 (-1)).mp hstep
    rcases hbottom hyy with hbefore | hafter
    · have h₁ := squareRegionCells_bottom_before_mem N l S hleft u.val.1 (by omega) (by omega) hbefore
      have h₂ := squareRegionCells_bottom_before_mem N l S hleft (u.val.1-1) (by omega) (by omega) (by omega)
      exact hcut (propext ⟨fun _ => h₂,fun _ => h₁⟩)
    · have h₁ := squareRegionCells_bottom_after_not_mem N r S hright u.val.1 (by omega) (by omega) (by omega)
      have h₂ := squareRegionCells_bottom_after_not_mem N r S hright (u.val.1-1) (by omega) (by omega) (by omega)
      exact hcut (propext ⟨fun hm => (h₁ hm).elim,fun hm => (h₂ hm).elim⟩)
  rw [mem_latticeRectangle]
  constructor <;> constructor <;> dsimp <;> omega

end
end PottsContinuity.Push
