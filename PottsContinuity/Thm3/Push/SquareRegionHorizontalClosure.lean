module

public import PottsContinuity.Thm3.Push.SquareRegionSideClosure
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Constant labels on the exterior left/right columns prevent EVERY full
cell-boundary neighbor from escaping horizontally, including at all four
original corner vertices. No vertical confinement premise is required. -/
theorem squareRegionCell_neighbor_horizontal_bounds
    (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v : RectangleDualVertex (0,0) N N, v.val.1 = -1 → v ∈ S)
    (hright : ∀ v : RectangleDualVertex (0,0) N N, v.val.1 = (N : ℤ) → v ∉ S)
    (u : RectangleVertex (0,0) N N)
    (v : LatticeVertex)
    (hxy : (latticeCellBoundaryGraph (squareRegionCells N S)).Adj u.val v) :
    0 ≤ v.1 ∧ v.1 ≤ (N : ℤ) := by
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
    have h₁ := squareRegionCells_left_mem N S hleft u.val.2 (by omega) (by omega)
    have h₂ := squareRegionCells_left_mem N S hleft (u.val.2-1) (by omega) (by omega)
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
    have h₁ := squareRegionCells_right_not_mem N S hright u.val.2 (by omega) (by omega)
    have h₂ := squareRegionCells_right_not_mem N S hright (u.val.2-1) (by omega) (by omega)
    exact hcut (propext ⟨fun hm => (h₁ hm).elim,fun hm => (h₂ hm).elim⟩)
  exact ⟨hxlo,hxhi⟩

end
end PottsContinuity.Push
