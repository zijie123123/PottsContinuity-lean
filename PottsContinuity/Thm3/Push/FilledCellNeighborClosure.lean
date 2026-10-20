module

public import PottsContinuity.Thm3.Push.FilledFaceBoundaryRows
public import PottsContinuity.Thm3.Push.FilledCellGraphBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Away from the physical left/right sides, the FULL cell-boundary graph
has no neighbor outside the original rectangle. This retains the actual
bottom/top port labels instead of assuming random-domain containment. -/
theorem filledCell_neighbor_mem_rectangle_off_sides (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (u : RectangleVertex a w h) (hl : a.1 < u.val.1) (hr : u.val.1 < a.1+(w : ℤ))
    (v : LatticeVertex)
    (hxy : (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj u.val v) :
    v ∈ PD.FK.latticeRectangle a w h := by
  rcases u with ⟨⟨ux,uy⟩,humem⟩
  rcases v with ⟨vx,vy⟩
  change a.1 < ux at hl
  change ux < a.1+(w : ℤ) at hr
  change (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj (ux,uy) (vx,vy) at hxy
  have hu := (mem_latticeRectangle a (ux,uy) w h).mp humem
  have hd : |ux-vx|+|uy-vy|=1 := latticeCellBoundaryGraph_le _ hxy
  have hdist := hd
  simp only [abs_eq_max_neg] at hdist
  have hylo : a.2 ≤ vy := by
    by_contra hbad
    have heq : vx=ux ∧ uy=a.2 ∧ vy=a.2-1 := by omega
    rcases heq with ⟨hxx,hyy,hvy⟩
    rw [hxx,hyy,hvy] at hxy
    have hstep : (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj
        (ux,a.2-1) (ux,(a.2-1)+1) := by simpa only [sub_add_cancel] using hxy.symm
    have hcut := (cellBoundary_adj_up_iff _ ux (a.2-1)).mp hstep
    have h₁ := rectangleFilledFaceCells_bottom_not_mem a w h A hA ux (by omega) hr
    have h₂ := rectangleFilledFaceCells_bottom_not_mem a w h A hA (ux-1) (by omega) (by omega)
    exact hcut (propext ⟨fun hm => (h₁ hm).elim,fun hm => (h₂ hm).elim⟩)
  have hyhi : vy ≤ a.2+(h : ℤ) := by
    by_contra hbad
    have heq : vx=ux ∧ uy=a.2+(h : ℤ) ∧ vy=(a.2+(h : ℤ))+1 := by omega
    rcases heq with ⟨hxx,hyy,hvy⟩
    rw [hxx,hyy,hvy] at hxy
    have hcut := (cellBoundary_adj_up_iff _ ux (a.2+(h : ℤ))).mp hxy
    have h₁ := rectangleFilledFaceCells_top a w h A ux (by omega) hr
    have h₂ := rectangleFilledFaceCells_top a w h A (ux-1) (by omega) (by omega)
    exact hcut (propext ⟨fun _ => h₂,fun _ => h₁⟩)
  rw [mem_latticeRectangle]
  exact ⟨⟨by omega,by omega⟩,hylo,hyhi⟩

end
end PottsContinuity.Push
