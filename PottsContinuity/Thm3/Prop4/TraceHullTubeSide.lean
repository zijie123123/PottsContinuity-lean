module

public import PottsContinuity.Thm3.Prop4.TubeVerticalOrder
public import PottsContinuity.Thm3.Prop4.SourceMiddleDomain

/-! # Filled trace access regions retain the source side outside the tube -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- A box vertex cut off from the bottom lies above a trace vertex in its
own column. The avoiding path uses only literal original lattice vertices. -/
theorem traceBottomInaccessible_column_witness (n : ℕ) (trace : Finset LatticeVertex)
    (z : LatticeVertex) (hzB : z ∈ box n) (hno : ¬traceBottomAccessible n trace z) :
    ∃ w ∈ trace, z.1 = w.1 ∧ w.2 ≤ z.2 := by
  classical
  by_contra hh
  have havoid : ∀ w : LatticeVertex, w.1 = z.1 → w.2 ≤ z.2 → w ∉ trace := by
    intro w hwx hwy hw
    exact hh ⟨w,hw,hwx.symm,hwy⟩
  have hzcoord : -(n : ℤ) ≤ z.1 ∧ z.1 ≤ n ∧ -(n : ℤ) ≤ z.2 ∧ z.2 ≤ n := by
    simpa only [box,Finset.mem_product,Finset.mem_Icc,and_assoc] using hzB
  obtain ⟨p,hp⟩ := PlanarTopology.vertical_walk_between z.1 (-(n : ℤ)) z.2
  simp only [min_eq_left hzcoord.2.2.1,max_eq_right hzcoord.2.2.1] at hp
  let q := p.reverse.copy (Prod.eta z) rfl
  apply hno
  refine ⟨(z.1,-(n : ℤ)),rfl,q,?_⟩
  intro w hw
  have hw' : w ∈ p.support := by
    simpa only [q,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
  obtain ⟨hwx,hwylo,hwyhi⟩ := hp w hw'
  refine ⟨?_,havoid w hwx hwyhi⟩
  simp only [box,Finset.mem_product,Finset.mem_Icc]
  exact ⟨by simpa only [hwx] using And.intro hzcoord.1 hzcoord.2.1,⟨hwylo,hwyhi.trans hzcoord.2.2.2⟩⟩

/-- A lower filled-hull vertex outside the exact Euclidean tube is on the
lower affine side whenever the trace is confined to the tube or below it. -/
theorem lowerTraceHull_outside_tube_nonpos {n : ℕ} (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 < R) (u v : LatticeVertex)
    (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.2 : ℝ) = t*u.1+b) (hvt : (v.2 : ℝ) = t*v.1+b)
    (trace : Finset LatticeVertex)
    (htrace : ∀ w ∈ trace, w ∈ radiusTube n R u v ∨ (w.2 : ℝ)-(t*w.1+b) ≤ 0)
    (z : LatticeVertex) (hz : z ∈ lowerTraceHull n trace) (hout : z ∉ radiusTube n R u v) :
    (z.2 : ℝ)-(t*z.1+b) ≤ 0 := by
  classical
  by_contra hh
  have hpos : 0 < (z.2 : ℝ)-(t*z.1+b) := lt_of_not_ge hh
  obtain ⟨w,hw,hx,hzw⟩ := lowerTraceHull_column_witness n trace z hz
  have hzB := (Finset.mem_filter.mp hz).1
  rcases htrace w hw with hwT | hwlo
  · have hwpoint : (z.1,w.2) = w := Prod.ext hx rfl
    have hzT := radiusTube_vertical_down_towards_line hn R hR u v hu hv t b hut hvt
      z.1 w.2 z.2 (by simpa only [Prod.eta] using hzB) (hwpoint.symm ▸ hwT) hzw (by linarith only [hpos])
    exact hout (by simpa only [Prod.eta] using hzT)
  · have hy : (z.2 : ℝ) ≤ w.2 := by exact_mod_cast hzw
    rw [← hx] at hwlo
    linarith only [hpos,hwlo,hy]

/-- A vertex cut off from bottom access is on the upper side outside the
same exact tube whenever its trace lies in the tube or on the upper side. -/
theorem traceBottomInaccessible_outside_tube_nonneg {n : ℕ} (hn : 1 ≤ n)
    (R : ℝ) (hR : 0 < R) (u v : LatticeVertex)
    (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.2 : ℝ) = t*u.1+b) (hvt : (v.2 : ℝ) = t*v.1+b)
    (trace : Finset LatticeVertex)
    (htrace : ∀ w ∈ trace, w ∈ radiusTube n R u v ∨ 0 ≤ (w.2 : ℝ)-(t*w.1+b))
    (z : LatticeVertex) (hzB : z ∈ box n) (hno : ¬traceBottomAccessible n trace z)
    (hout : z ∉ radiusTube n R u v) : 0 ≤ (z.2 : ℝ)-(t*z.1+b) := by
  by_contra hh
  have hneg : (z.2 : ℝ)-(t*z.1+b) < 0 := lt_of_not_ge hh
  obtain ⟨w,hw,hx,hwz⟩ := traceBottomInaccessible_column_witness n trace z hzB hno
  rcases htrace w hw with hwT | hwhi
  · have hwpoint : (z.1,w.2) = w := Prod.ext hx rfl
    have hzT := radiusTube_vertical_up_towards_line hn R hR u v hu hv t b hut hvt
      z.1 w.2 z.2 (by simpa only [Prod.eta] using hzB) (hwpoint.symm ▸ hwT) hwz (by linarith only [hneg])
    exact hout (by simpa only [Prod.eta] using hzT)
  · have hy : (w.2 : ℝ) ≤ z.2 := by exact_mod_cast hwz
    rw [← hx] at hwhi
    linarith only [hneg,hwhi,hy]

end
end PottsContinuity.Thm3.Prop4
