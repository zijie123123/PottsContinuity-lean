module

public import PottsContinuity.Thm3.Push.IntervalArmUpperIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance upperCutPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- For an upward-half-strip closed walk whose original square bonds lie on the filled cut, each
cut bond sees index zero on BOTH adjacent faces: one reaches an opposite exterior seed,
the other belongs to the actual left-reached cluster. -/
theorem upper_strip_cut_bond_face_indices_eq (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, 0 ≤ x.1 ∧ x.1 ≤ (N : ℤ) ∧ 0 ≤ x.2)
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
      exact (rayIndex_upper_strip_right_region_zero N l r A p hinside hedges u hu).trans
        (rayIndex_upper_strip_left_reached_zero N l r A p hinside hedges v hvs).symm
    · have hv : v ∈ intervalArmRightRegion N l r A := by
        by_contra hv
        exact hne (by simp only [hu,hv,not_false_eq_true,decide_true])
      have hus := outsideSeedRegion_boundary_in_original _ _ _ hv hu hadj.symm
      exact (rayIndex_upper_strip_left_reached_zero N l r A p hinside hedges u hus).trans
        (rayIndex_upper_strip_right_region_zero N l r A p hinside hedges v hv).symm
  have hs : u.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase false :=
    rectangleDualEdgeSource_faceBase (0,0) N N d
  have ht : v.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase true :=
    rectangleDualEdgeTarget_faceBase (0,0) N N d
  rw [← hs,← ht]
  exact hidx

/-- A closed edge-simple walk in the upward half strip cannot use ANY
original square bond if all its original-square bonds lie on the filled cut.
Edges above the square remain permitted in the walk. -/
theorem upper_strip_closed_trail_avoids_interval_square_bonds (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hn : p.edges.Nodup)
    (hinside : ∀ x ∈ p.support, 0 ≤ x.1 ∧ x.1 ≤ (N : ℤ) ∧ 0 ≤ x.2)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∉ p.edges := by
  intro hf
  exact (rayIndex_bond_faces_ne_of_mem p hn (rectanglePrimalEdgeBond (0,0) N N f) hf)
    (upper_strip_cut_bond_face_indices_eq N l r A p hinside hedges f (hedges f hf))

end
end PottsContinuity.Push
