module

public import PottsContinuity.Thm3.Push.UpperBandDualWalk
public import PottsContinuity.Thm3.Push.FirstArrivalDown
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- A crossing of the upper band prevents the full reference rectangle's
top closed-dual cluster from reaching the band's bottom port row or below.
The closed-dual path is truncated at FIRST arrival before transport to the
band's true complementary dual. -/
theorem rectangle_topReached_above_upper_band_bottom
    (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H)
    (A : Configuration (rectangleGraph a w H))
    (hcross : DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t))
    (v : RectangleDualVertex a w H) (hv : v ∈ rectangleTopReached a w H A) :
    a.2+(t : ℤ) ≤ v.val.2 := by
  by_contra hlow
  obtain ⟨u,hu,hconn⟩ := hv
  rw [auxiliaryClosedConfiguration_rectangle_eq] at hconn
  obtain ⟨p⟩ := hconn
  have huy : u.val.2=a.2+(H : ℤ) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rfl
  have hstep : ∀ x y : RectangleDualVertex a w H,
      (openGraph (rectangleDualGraph a w H) (rectangleDualConfiguration a w H A)).Adj x y →
      |x.val.2-y.val.2| ≤ 1 := by
    intro x y hxy
    exact (rectangle_dual_step_height_and_column a w H (openGraph_le _ _ hxy)).1
  obtain ⟨z,r,s,hzy,hp,hfirst⟩ := walk_first_arrival_down
    (fun x : RectangleDualVertex a w H => x.val.2) hstep p (a.2+(t : ℤ)-1)
    (by omega) (by omega)
  have hsub : ((H-t : ℕ) : ℤ)=(H : ℤ)-(t : ℤ) := Nat.cast_sub ht
  have hmem : ∀ x : RectangleDualVertex a w H,
      a.2+(t : ℤ)-1 ≤ x.val.2 →
      x.val ∈ rectangleDualExpanded (a.1,a.2+(t : ℤ)) w (H-t) := by
    intro x hx
    have hprops := (mem_latticeRectangle (a.1-1,a.2-1) x.val (w+1) (H+1)).mp x.property
    rw [rectangleDualExpanded,mem_latticeRectangle]
    simp only [Nat.cast_add,Nat.cast_one] at hprops ⊢
    exact ⟨hprops.1,hx,by omega⟩
  let U : RectangleDualVertex (a.1,a.2+(t : ℤ)) w (H-t) := ⟨u.val,hmem u (by omega)⟩
  let Z : RectangleDualVertex (a.1,a.2+(t : ℤ)) w (H-t) := ⟨z.val,hmem z hzy.ge⟩
  let ι := rectangleDualVertexEmbedding (rectangle_dual_upper_band_subset a w H t ht)
  have hU : ι U=u := Subtype.ext rfl
  have hZ : ι Z=z := Subtype.ext rfl
  let rr := r.copy hU.symm hZ.symm
  have hlo : ∀ x ∈ rr.support, a.2+(t : ℤ)-1 ≤ x.val.2 := by
    intro x hx
    have hxr : x ∈ r.support := by simpa only [rr,SimpleGraph.Walk.support_copy] using hx
    by_contra hbad
    have hxz := hfirst x hxr (by omega)
    rw [hxz,hzy] at hbad
    exact hbad (le_refl _)
  have hbottom : ∀ x ∈ rr.support, ∀ y ∈ rr.support,
      x.val.2=a.2+(t : ℤ)-1 → y.val.2=a.2+(t : ℤ)-1 → x=y := by
    intro x hx y hy hxb hyb
    have hxr : x ∈ r.support := by simpa only [rr,SimpleGraph.Walk.support_copy] using hx
    have hyr : y ∈ r.support := by simpa only [rr,SimpleGraph.Walk.support_copy] using hy
    exact (hfirst x hxr hxb.le).trans (hfirst y hyr hyb.le).symm
  obtain ⟨q,hq⟩ := upper_band_closed_dual_walk_pullback a w H t ht A U Z rr hlo hbottom
  apply rectanglePrimalDualCrossings_exclusive (a.1,a.2+(t : ℤ)) w (H-t)
    (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht) A) hcross
  refine ⟨Z,U,hzy,?_,⟨q.reverse⟩⟩
  change u.val.2=(a.2+(t : ℤ))+((H-t : ℕ) : ℤ)
  omega

end
end PottsContinuity.Push
