module

public import PottsContinuity.Thm3.Push.FilledCellNeighborClosure
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- In the proof by contradiction for a frontier component detached from the
physical sides, all paths of the FULL cell-boundary component lift back to
actual frontier paths in the rectangle. This is the component-local closure
needed to extract a genuine interior cycle; detachedness is not asserted. -/
theorem filledCell_reachable_lift_of_no_side_connection (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (u : RectangleVertex a w h)
    (hdetached : ∀ v : RectangleVertex a w h,
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) →
      ¬ ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) u v)
    (z : LatticeVertex)
    (hreach : (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Reachable u.val z) :
    ∃ v : RectangleVertex a w h, v.val=z ∧
      ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact ⟨u,rfl,SimpleGraph.Reachable.rfl⟩
  | @tail x z hprefix hxz ih =>
    obtain ⟨v,hvx,huv⟩ := ih
    have hprops := (mem_latticeRectangle a v.val w h).mp v.property
    have hneL : v.val.1 ≠ a.1 := fun hv => hdetached v (Or.inl hv) huv
    have hneR : v.val.1 ≠ a.1+(w : ℤ) := fun hv => hdetached v (Or.inr hv) huv
    have hleft : a.1 < v.val.1 := by omega
    have hright : v.val.1 < a.1+(w : ℤ) := by omega
    have hcell : (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Adj v.val z := by
      rw [hvx]
      exact hxz
    have hz := filledCell_neighbor_mem_rectangle_off_sides a w h A hA v hleft hright z hcell
    let v' : RectangleVertex a w h := ⟨z,hz⟩
    have hfront : (openGraph (rectangleGraph a w h)
        (rectangleFilledTopFrontier a w h A)).Adj v v' :=
      (filledTopFrontier_adj_iff_cellBoundary a w h A v v').mp hcell
    exact ⟨v',rfl,huv.trans hfront.reachable⟩

end
end PottsContinuity.Push
