module

public import PottsContinuity.Thm3.Push.IntervalArmFilledIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance intervalFilledNoCyclePropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- For a rectangle-confined closed walk supported on the filled cut, each
cut bond sees index zero on BOTH adjacent faces: one reaches an opposite exterior seed,
the other belongs to the actual left-reached cluster. -/
theorem interval_filled_cut_bond_face_indices_eq (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle (0,0) N N)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges → f ∈ intervalArmFilledLeftFrontier N l r A)
    (f : (rectangleGraph (0,0) N N).edgeSet) (hf : f ∈ intervalArmFilledLeftFrontier N l r A) :
    rayIndex (faceIndexMark ((rectanglePrimalEdgeBond (0,0) N N f).faceBase false)) p =
      rayIndex (faceIndexMark ((rectanglePrimalEdgeBond (0,0) N N f).faceBase true)) p := by
  let e := DualityExt.rectangleDualEdgeEquiv (0,0) N N
  let d := rectanglePrimalDualEdgeEquiv (0,0) N N f
  let u := rectangleDualEdgeSource (0,0) N N d
  let v := rectangleDualEdgeTarget (0,0) N N d
  have hne : decide (u ∉ intervalArmRightRegion N l r A) ≠
      decide (v ∉ intervalArmRightRegion N l r A) :=
    (mem_auxiliaryLabelCut_iff e _ f u v (by rfl)).mp hf
  have hadj : (rectangleDualGraph (0,0) N N).Adj u v := (e f).property
  have hidx : rayIndex (faceIndexMark u.val) p = rayIndex (faceIndexMark v.val) p := by
    by_cases hu : u ∈ intervalArmRightRegion N l r A
    · have hv : v ∉ intervalArmRightRegion N l r A := by
        intro hv
        exact hne (by simp only [hu,hv,not_true_eq_false,decide_false])
      have hvs := outsideSeedRegion_boundary_in_original _ _ _ hu hv hadj
      exact (rayIndex_zero_on_interval_right_region N l r A p hinside hedges u hu).trans
        (rayIndex_zero_on_interval_left_reached N l r A p hinside hedges v hvs).symm
    · have hv : v ∈ intervalArmRightRegion N l r A := by
        by_contra hv
        exact hne (by simp only [hu,hv,not_false_eq_true,decide_true])
      have hus := outsideSeedRegion_boundary_in_original _ _ _ hv hu hadj.symm
      exact (rayIndex_zero_on_interval_left_reached N l r A p hinside hedges u hus).trans
        (rayIndex_zero_on_interval_right_region N l r A p hinside hedges v hv).symm
  have hs : u.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase false :=
    rectangleDualEdgeSource_faceBase (0,0) N N d
  have ht : v.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase true :=
    rectangleDualEdgeTarget_faceBase (0,0) N N d
  rw [← hs,← ht]
  exact hidx

/-- A closed edge-simple walk supported on the filled interval-arm frontier cannot be
nonempty. This proves the winding contradiction rather than assuming an
extremal-path separation property. -/
theorem interval_filled_frontier_closed_trail_length_zero (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hn : p.edges.Nodup)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle (0,0) N N)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges → f ∈ intervalArmFilledLeftFrontier N l r A) :
    p.length = 0 := by
  cases p with
  | nil => rfl
  | @cons z v z hzv p =>
    have hzmem := hinside z (p.cons hzv).start_mem_support
    have hvmem := hinside v (by
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons]
      exact Or.inr p.start_mem_support)
    let u₀ : RectangleVertex (0,0) N N := ⟨z,hzmem⟩
    let v₀ : RectangleVertex (0,0) N N := ⟨v,hvmem⟩
    have huv : (rectangleGraph (0,0) N N).Adj u₀ v₀ := (rectangleGraph_adj_iff (0,0) N N u₀ v₀).mpr hzv
    let f : (rectangleGraph (0,0) N N).edgeSet := ⟨s(u₀,v₀),(rectangleGraph (0,0) N N).mem_edgeSet.mpr huv⟩
    have heq : (rectanglePrimalEdgeBond (0,0) N N f).toSym2 = s(z,v) :=
      rectanglePrimalEdgeBond_toSym2_public (0,0) N N f
    have he : (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ (p.cons hzv).edges := by
      rw [heq]
      exact List.mem_cons_self
    have hidx := interval_filled_cut_bond_face_indices_eq N l r A (p.cons hzv) hinside hedges f (hedges f he)
    exact ((rayIndex_bond_faces_ne_of_mem (p.cons hzv) hn (rectanglePrimalEdgeBond (0,0) N N f) he) hidx).elim

end
end PottsContinuity.Push
