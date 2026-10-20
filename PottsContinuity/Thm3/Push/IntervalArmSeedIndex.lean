module

public import PottsContinuity.Thm3.Push.IntervalArmFilledExploration
public import PottsContinuity.Thm3.Push.AuxiliaryIndexInvariance
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance seedIndexPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Index zero propagates from the actual reached left seeds along closed-dual
paths when the primal closed walk is supported on original square bonds of the filled source frontier. -/
theorem rayIndex_left_reached_of_seed_zero (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hseed : ∀ b ∈ intervalArmLeftDualPorts N l, rayIndex (faceIndexMark b.val) p=0)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmLeftReached N l A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨b,hb,⟨q⟩⟩ := hv
  let S := intervalArmLeftReached N l A
  let H := rectangleDualGraph (0,0) N N
  let σ := fun x => decide (x ∉ intervalArmRightRegion N l r A)
  let qH := q.mapLe (openGraph_le H _)
  have hsupport : ∀ x ∈ qH.support, x ∈ S := by
    intro x hx
    have hx' : x ∈ q.support := by simpa only [qH,SimpleGraph.Walk.support_mapLe_eq_support] using hx
    exact ⟨b,hb,(q.takeUntil x hx').reachable⟩
  let qS := qH.induce S hsupport
  have hlabel : ∀ x ∈ S, σ x = true := by
    intro x hxs
    apply decide_eq_true
    exact fun hright => (outsideSeedRegion_subset_compl _ _ _ hright) hxs
  have hidx := rectangle_constant_region_index_eq (0,0) N N σ p hedges S true hlabel qS.reachable
  exact hidx.symm.trans (hseed b hb)

/-- Index zero propagates through the geometric opposite-region paths.
Those paths are not required to consist of closed dual edges. -/
theorem rayIndex_right_region_of_seed_zero (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hseed : ∀ b ∈ intervalArmRightDualPorts N r, rayIndex (faceIndexMark b.val) p=0)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (v : RectangleDualVertex (0,0) N N) (hv : v ∈ intervalArmRightRegion N l r A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨b,hb,hbs,hvs,⟨q⟩⟩ := hv
  let S := intervalArmLeftReached N l A
  let C := intervalArmRightRegion N l r A
  let H := rectangleDualGraph (0,0) N N
  let σ := fun x => decide (x ∉ C)
  let inclusion : H.induce Sᶜ →g H := {toFun := Subtype.val,map_rel' := fun h => h}
  let qH := q.map inclusion
  have hsupport : ∀ x ∈ qH.support, x ∈ C := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
    exact ⟨b,hb,hbs,t.property,(q.takeUntil t ht).reachable⟩
  let qC := qH.induce C hsupport
  have hlabel : ∀ x ∈ C, σ x = false := by
    intro x hxc
    exact decide_eq_false (not_not_intro hxc)
  have hidx := rectangle_constant_region_index_eq (0,0) N N σ p hedges C false hlabel qC.reachable
  exact hidx.symm.trans (hseed b hb)

/-- For a closed walk whose original square bonds lie on the filled cut and whose prescribed seed marks have zero index, each
cut bond sees index zero on BOTH adjacent faces: one reaches an opposite exterior seed,
the other belongs to the actual left-reached cluster. -/
theorem cut_bond_face_indices_eq_of_seed_zero (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hleft : ∀ b ∈ intervalArmLeftDualPorts N l, rayIndex (faceIndexMark b.val) p=0)
    (hright : ∀ b ∈ intervalArmRightDualPorts N r, rayIndex (faceIndexMark b.val) p=0)
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
      exact (rayIndex_right_region_of_seed_zero N l r A p hright hedges u hu).trans
        (rayIndex_left_reached_of_seed_zero N l r A p hleft hedges v hvs).symm
    · have hv : v ∈ intervalArmRightRegion N l r A := by
        by_contra hv
        exact hne (by simp only [hu,hv,not_false_eq_true,decide_true])
      have hus := outsideSeedRegion_boundary_in_original _ _ _ hv hu hadj.symm
      exact (rayIndex_left_reached_of_seed_zero N l r A p hleft hedges u hus).trans
        (rayIndex_right_region_of_seed_zero N l r A p hright hedges v hv).symm
  have hs : u.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase false :=
    rectangleDualEdgeSource_faceBase (0,0) N N d
  have ht : v.val = (rectanglePrimalEdgeBond (0,0) N N f).faceBase true :=
    rectangleDualEdgeTarget_faceBase (0,0) N N d
  rw [← hs,← ht]
  exact hidx

/-- A closed edge-simple walk with zero seed indices cannot use ANY original
square bond if all its original-square bonds lie on the actual filled cut. -/
theorem closed_trail_avoids_interval_square_bonds_of_seed_zero (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) {z : LatticeVertex}
    (p : squareLattice.Walk z z) (hn : p.edges.Nodup)
    (hleft : ∀ b ∈ intervalArmLeftDualPorts N l, rayIndex (faceIndexMark b.val) p=0)
    (hright : ∀ b ∈ intervalArmRightDualPorts N r, rayIndex (faceIndexMark b.val) p=0)
    (hedges : ∀ f : (rectangleGraph (0,0) N N).edgeSet,
      (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∈ p.edges →
        f ∈ intervalArmFilledLeftFrontier N l r A)
    (f : (rectangleGraph (0,0) N N).edgeSet) :
    (rectanglePrimalEdgeBond (0,0) N N f).toSym2 ∉ p.edges := by
  intro hf
  exact (rayIndex_bond_faces_ne_of_mem p hn (rectanglePrimalEdgeBond (0,0) N N f) hf)
    (cut_bond_face_indices_eq_of_seed_zero N l r A p hleft hright hedges f (hedges f hf))


end
end PottsContinuity.Push
