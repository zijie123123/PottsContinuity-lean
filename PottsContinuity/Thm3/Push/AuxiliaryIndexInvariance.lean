module

public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.Thm3.Push.RectangleLabelFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section

/-- A same-label true-dual edge avoids a primal walk supported on the label
cut, hence preserves its ray index. The (1,1) mark shift is retained exactly. -/
theorem rectangle_same_label_adj_index_eq (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleDualVertex a w h → Bool) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges →
        f ∈ auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h) σ)
    {u v : RectangleDualVertex a w h} (huv : (rectangleDualGraph a w h).Adj u v)
    (hlabels : σ u = σ v) :
    rayIndex (faceIndexMark u.val) p = rayIndex (faceIndexMark v.val) p := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  let g : (rectangleDualGraph a w h).edgeSet := ⟨s(u,v),(rectangleDualGraph a w h).mem_edgeSet.mpr huv⟩
  let f := e.symm g
  let d := rectanglePrimalDualEdgeEquiv a w h f
  have hp : (e f).val=s(u,v) := by
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
  have hnot : (rectanglePrimalEdgeBond a w h f).toSym2 ∉ p.edges := by
    intro he
    have hcut := (mem_auxiliaryLabelCut_iff e σ f u v hp).mp (hedges f he)
    exact hcut hlabels
  have hidx := rayIndex_bond_faces_eq_of_not_mem p (rectanglePrimalEdgeBond a w h f) hnot
  have hs : (rectangleDualEdgeSource a w h d).val =
      (rectanglePrimalEdgeBond a w h f).faceBase false := rectangleDualEdgeSource_faceBase a w h d
  have ht : (rectangleDualEdgeTarget a w h d).val =
      (rectanglePrimalEdgeBond a w h f).faceBase true := rectangleDualEdgeTarget_faceBase a w h d
  rw [← hs,← ht] at hidx
  have hpair : s(rectangleDualEdgeSource a w h d,rectangleDualEdgeTarget a w h d)=s(u,v) := hp
  rcases Sym2.eq_iff.mp hpair with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · simpa only [hu,hv] using hidx
  · have hi : rayIndex (faceIndexMark v.val) p = rayIndex (faceIndexMark u.val) p := by
      simpa only [hu,hv] using hidx
    exact hi.symm

/-- The index is constant along an underlying dual path contained in any
constant-label region. This uses no open/closed status for those dual edges. -/
theorem rectangle_constant_region_index_eq (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleDualVertex a w h → Bool) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges →
        f ∈ auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h) σ)
    (R : Set (RectangleDualVertex a w h)) (b : Bool)
    (hR : ∀ v ∈ R, σ v=b) {u v : R}
    (hconn : ((rectangleDualGraph a w h).induce R).Reachable u v) :
    rayIndex (faceIndexMark u.val.val) p = rayIndex (faceIndexMark v.val.val) p := by
  obtain ⟨q⟩ := hconn
  induction q with
  | nil => rfl
  | @cons u t v hut q ih =>
    have hidx := rectangle_same_label_adj_index_eq a w h σ p hedges hut
      ((hR u.val u.property).trans (hR t.val t.property).symm)
    exact hidx.trans ih

end
end PottsContinuity.Push
