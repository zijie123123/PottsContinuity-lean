module

public import PottsContinuity.Thm3.Push.AuxiliaryIndexInvariance
public import PottsContinuity.Thm3.Push.RectangleFilledFrontier
public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality
noncomputable section
local instance regionIndexPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- Bottom-port marks lie below every vertex of a rectangle-confined walk. -/
theorem rayIndex_rectangle_bottom_port_zero (a : LatticeVertex) (w h : ℕ)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (b : RectangleDualVertex a w h) (hb : b ∈ rectangleDualBottomPorts a w h) :
    rayIndex (faceIndexMark b.val) p = 0 := by
  have hby : b.val.2 = a.2-1 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    rfl
  apply rayIndex_zero_of_level _ p 0
  intro x hx
  have hy := ((mem_latticeRectangle a x w h).mp (hinside x hx)).2.1
  simp only [faceIndexMark,hby,sub_add_cancel]
  rw [ite_eq_right (by omega)]

/-- Top-port marks lie above every vertex of a rectangle-confined walk. -/
theorem rayIndex_rectangle_top_port_zero (a : LatticeVertex) (w h : ℕ)
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (t : RectangleDualVertex a w h) (ht : t ∈ rectangleDualTopPorts a w h) :
    rayIndex (faceIndexMark t.val) p = 0 := by
  have hty : t.val.2 = a.2+(h : ℤ) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    rfl
  apply rayIndex_zero_of_level _ p 1
  intro x hx
  have hy := ((mem_latticeRectangle a x w h).mp (hinside x hx)).2.2
  simp only [faceIndexMark,hty]
  rw [ite_eq_left (by omega)]

/-- Index zero propagates from top ports along the ACTUAL explored closed-dual
clusters whenever the primal walk is supported on the filled frontier. -/
theorem rayIndex_zero_on_top_reached (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ rectangleFilledTopFrontier a w h A)
    (v : RectangleDualVertex a w h) (hv : v ∈ rectangleTopReached a w h A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨t,ht,⟨q⟩⟩ := hv
  let S := rectangleTopReached a w h A
  let H := rectangleDualGraph a w h
  let σ := fun x => decide (x ∉ rectangleBottomRegion a w h A)
  let qH := q.mapLe (openGraph_le H _)
  have hsupport : ∀ x ∈ qH.support, x ∈ S := by
    intro x hx
    have hx' : x ∈ q.support := by simpa only [qH,SimpleGraph.Walk.support_mapLe_eq_support] using hx
    exact ⟨t,ht,(q.takeUntil x hx').reachable⟩
  let qS := qH.induce S hsupport
  have hlabel : ∀ x ∈ S, σ x = true := by
    intro x hxs
    apply decide_eq_true
    intro hbot
    exact (outsideSeedRegion_subset_compl _ _ _ hbot) hxs
  have hidx := rectangle_constant_region_index_eq a w h σ p hedges S true hlabel qS.reachable
  exact hidx.symm.trans (rayIndex_rectangle_top_port_zero a w h p hinside t ht)

/-- Index zero propagates from bottom ports through the underlying bottom
region. These paths are geometric and are not asserted to be dual-open. -/
theorem rayIndex_zero_on_bottom_region (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {z : LatticeVertex}
    (p : squareLattice.Walk z z)
    (hinside : ∀ x ∈ p.support, x ∈ PD.FK.latticeRectangle a w h)
    (hedges : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ rectangleFilledTopFrontier a w h A)
    (v : RectangleDualVertex a w h) (hv : v ∈ rectangleBottomRegion a w h A) :
    rayIndex (faceIndexMark v.val) p = 0 := by
  obtain ⟨b,hb,hbs,hvs,⟨q⟩⟩ := hv
  let S := rectangleTopReached a w h A
  let C := rectangleBottomRegion a w h A
  let H := rectangleDualGraph a w h
  let σ := fun x => decide (x ∉ C)
  let inclusion : H.induce Sᶜ →g H := {toFun := Subtype.val,map_rel' := fun hstep => hstep}
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
  have hidx := rectangle_constant_region_index_eq a w h σ p hedges C false hlabel qC.reachable
  exact hidx.symm.trans (rayIndex_rectangle_bottom_port_zero a w h p hinside b hb)

end
end PottsContinuity.Push
