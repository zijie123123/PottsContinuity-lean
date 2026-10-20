module

public import PottsContinuity.Thm3.Push.DetachedFrontierPaths
public import PottsContinuity.PD.Duality.FiniteSupportEvenEdgeCycle
public import PottsContinuity.PD.Duality.LatticeCellBoundaryFiniteEdges
public import PottsContinuity.PD.Duality.LatticeCellBoundaryParity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Contradiction step for a filled-frontier component detached from both
physical sides: every edge of that component lies on a real simple cell-boundary
cycle which stays inside the original rectangle. No such component is asserted
to exist; the detachedness premise is to be contradicted by winding. -/
theorem detached_filledFrontier_has_interior_cycle (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (u v : RectangleVertex a w h)
    (huv : (openGraph (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A)).Adj u v)
    (hdetached : ∀ t : RectangleVertex a w h,
      (t.val.1=a.1 ∨ t.val.1=a.1+(w : ℤ)) →
      ¬ ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) u t) :
    ∃ p : (latticeCellBoundaryGraph (rectangleFilledFaceCells a w h A)).Walk u.val u.val,
      p.IsCycle ∧ s(u.val,v.val) ∈ p.edges ∧
        ∀ z ∈ p.support, z ∈ PD.FK.latticeRectangle a w h := by
  classical
  let S := rectangleFilledFaceCells a w h A
  let C := latticeCellBoundaryGraph S
  have hcell : C.Adj u.val v.val := (filledTopFrontier_adj_iff_cellBoundary a w h A u v).mpr huv
  obtain ⟨z,p,hp,he⟩ := edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet C
    (latticeCellBoundaryGraph_edgeSet_finite S) (latticeCellBoundaryGraph_even_degree S) hcell
  have hus : u.val ∈ p.support :=
    SimpleGraph.Walk.mem_support_of_mem_edges he ((Sym2.mem_iff').mpr (Or.inl rfl))
  let q := p.rotate u.val hus
  refine ⟨q,hp.rotate hus,?_,?_⟩
  · exact (p.rotate_edges u.val hus).perm.mem_iff.mpr he
  · intro x hx
    have hreach : C.Reachable u.val x := (q.takeUntil x hx).reachable
    obtain ⟨t,ht,hut⟩ :=
      filledCell_reachable_lift_of_no_side_connection a w h A hA u hdetached x hreach
    exact ht ▸ t.property

end
end PottsContinuity.Push
