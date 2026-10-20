module

public import PottsContinuity.Thm3.Push.FilledRegionIndexZero
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance noCyclePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- For a rectangle-confined closed walk supported on the filled cut, each
cut bond sees index zero on BOTH adjacent faces: one reaches a bottom port,
the other belongs to the actual top-reached cluster. -/
theorem filled_cut_bond_face_indices_eq (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ rectangleFilledTopFrontier a w h A)
    (f : (rectangleGraph a w h).edgeSet) (hf : f ∈ rectangleFilledTopFrontier a w h A) :
    rayIndex (faceIndexMark ((rectanglePrimalEdgeBond a w h f).faceBase false)) p =
      rayIndex (faceIndexMark ((rectanglePrimalEdgeBond a w h f).faceBase true)) p := by
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  let d := rectanglePrimalDualEdgeEquiv a w h f
  let u := rectangleDualEdgeSource a w h d
  let v := rectangleDualEdgeTarget a w h d
  have hne : decide (u ∉ rectangleBottomRegion a w h A) ≠
      decide (v ∉ rectangleBottomRegion a w h A) :=
    (mem_auxiliaryLabelCut_iff e _ f u v (by rfl)).mp hf
  have hadj : (rectangleDualGraph a w h).Adj u v := (e f).property
  have hidx : rayIndex (faceIndexMark u.val) p = rayIndex (faceIndexMark v.val) p := by
    by_cases hu : u ∈ rectangleBottomRegion a w h A
    · have hv : v ∉ rectangleBottomRegion a w h A := by
        intro hv
        exact hne (by simp only [hu,hv,not_true_eq_false,decide_false])
      have hvs := outsideSeedRegion_boundary_in_original _ _ _ hu hv hadj
      exact (rayIndex_zero_on_bottom_region a w h A p hinside hedges u hu).trans
        (rayIndex_zero_on_top_reached a w h A p hinside hedges v hvs).symm
    · have hv : v ∈ rectangleBottomRegion a w h A := by
        by_contra hv
        exact hne (by simp only [hu,hv,not_false_eq_true,decide_true])
      have hus := outsideSeedRegion_boundary_in_original _ _ _ hv hu hadj.symm
      exact (rayIndex_zero_on_top_reached a w h A p hinside hedges u hus).trans
        (rayIndex_zero_on_bottom_region a w h A p hinside hedges v hv).symm
  have hs : u.val = (rectanglePrimalEdgeBond a w h f).faceBase false :=
    rectangleDualEdgeSource_faceBase a w h d
  have ht : v.val = (rectanglePrimalEdgeBond a w h f).faceBase true :=
    rectangleDualEdgeTarget_faceBase a w h d
  rw [← hs,← ht]
  exact hidx

/-- A closed edge-simple walk supported on the filled frontier cannot be
nonempty. This proves the winding contradiction rather than assuming an
extremal-path separation property. -/
theorem filled_frontier_closed_trail_length_zero (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hn : p.edges.Nodup)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ rectangleFilledTopFrontier a w h A) :
    p.length = 0 := by
  cases p with
  | nil => rfl
  | @cons z v z hzv p =>
    have hzmem := hinside z (p.cons hzv).start_mem_support
    have hvmem := hinside v (by
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons]
      exact Or.inr p.start_mem_support)
    let u₀ : RectangleVertex a w h := ⟨z,hzmem⟩
    let v₀ : RectangleVertex a w h := ⟨v,hvmem⟩
    have huv : (rectangleGraph a w h).Adj u₀ v₀ := (rectangleGraph_adj_iff a w h u₀ v₀).mpr hzv
    let f : (rectangleGraph a w h).edgeSet := ⟨s(u₀,v₀),(rectangleGraph a w h).mem_edgeSet.mpr huv⟩
    have heq : (rectanglePrimalEdgeBond a w h f).toSym2 = s(z,v) :=
      rectanglePrimalEdgeBond_toSym2_public a w h f
    have he : (rectanglePrimalEdgeBond a w h f).toSym2 ∈ (p.cons hzv).edges := by
      rw [heq]
      exact List.mem_cons_self
    have hidx := filled_cut_bond_face_indices_eq a w h A (p.cons hzv) hinside hedges f (hedges f he)
    exact ((rayIndex_bond_faces_ne_of_mem (p.cons hzv) hn (rectanglePrimalEdgeBond a w h f) he) hidx).elim

end
end PottsContinuity.Push
