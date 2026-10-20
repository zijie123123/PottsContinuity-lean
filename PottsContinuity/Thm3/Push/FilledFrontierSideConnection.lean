module

public import PottsContinuity.Thm3.Push.DetachedFrontierCycle
public import PottsContinuity.Thm3.Push.FilledFrontierNoCycles
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- Every nontrivial filled-frontier component touches a physical left or
right side through ACTUAL frontier bonds. The proof rules out a detached
component by a real interior cycle and the proved index-jump contradiction. -/
theorem filled_frontier_adj_component_meets_side (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (u v : RectangleVertex a w h)
    (huv : (openGraph (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A)).Adj u v) :
    ∃ t : RectangleVertex a w h, (t.val.1=a.1 ∨ t.val.1=a.1+(w : ℤ)) ∧
      ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) u t := by
  classical
  by_contra hno
  have hdetached : ∀ t : RectangleVertex a w h,
      (t.val.1=a.1 ∨ t.val.1=a.1+(w : ℤ)) →
      ¬ ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) u t := by
    intro t ht hut
    exact hno ⟨t,ht,hut⟩
  obtain ⟨q,hq,he,hinside⟩ := detached_filledFrontier_has_interior_cycle a w h A hA u v huv hdetached
  let p := q.mapLe (latticeCellBoundaryGraph_le (rectangleFilledFaceCells a w h A))
  have hp : p.IsCycle := hq.mapLe _
  have hsupport : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h := by
    intro x hx
    exact hinside x (by simpa only [p,SimpleGraph.Walk.support_mapLe_eq_support] using hx)
  have hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges →
        f ∈ rectangleFilledTopFrontier a w h A := by
    intro f hf
    have hfq : (rectanglePrimalEdgeBond a w h f).toSym2 ∈ q.edges := by
      simpa only [p,SimpleGraph.Walk.edges_mapLe_eq_edges] using hf
    have hcell := q.edges_subset_edgeSet hfq
    rw [latticeCellBoundaryGraph_edgeSet_eq_image] at hcell
    obtain ⟨b,hb,hbf⟩ := hcell
    have hbEq : b=rectanglePrimalEdgeBond a w h f := LatticeBond.toSym2_injective hbf
    apply (mem_filledTopFrontier_iff_cellBoundary a w h A f).mpr
    simpa only [hbEq,Finset.mem_coe] using hb
  have hzero := filled_frontier_closed_trail_length_zero a w h A p hp.isTrail.edges_nodup hsupport hedges
  exact hp.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp hzero)

/-- Every vertex incident to a filled-frontier bond belongs to an actual
frontier component meeting one of the original wired sides. This is the
geometric input of the push argument. -/
theorem filled_frontier_bond_vertex_connects_to_side (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    (f : (rectangleGraph a w h).edgeSet) (hf : f ∈ rectangleFilledTopFrontier a w h A)
    (v : RectangleVertex a w h) (hv : v ∈ f.val) :
    ∃ t : RectangleVertex a w h, (t.val.1=a.1 ∨ t.val.1=a.1+(w : ℤ)) ∧
      ActualConnected (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A) v t := by
  let pair := f.val.out
  have hpair : s(pair.1,pair.2)=f.val := Quot.out_eq _
  have hadj : (openGraph (rectangleGraph a w h) (rectangleFilledTopFrontier a w h A)).Adj
      pair.1 pair.2 := by
    rw [openGraph_adj]
    exact ⟨f,hf,hpair.symm⟩
  rw [← hpair] at hv
  rcases (Sym2.mem_iff').mp hv with hv | hv
  · simpa only [hv] using filled_frontier_adj_component_meets_side a w h A hA pair.1 pair.2 hadj
  · simpa only [hv] using filled_frontier_adj_component_meets_side a w h A hA pair.2 pair.1 hadj.symm

end
end PottsContinuity.Push
