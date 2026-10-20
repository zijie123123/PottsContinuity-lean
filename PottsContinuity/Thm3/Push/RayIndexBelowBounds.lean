module

public import PottsContinuity.PD.Duality.RayIndexSeparation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.Duality

private theorem rayStep_eq_height_difference_of_below_left
    (v u w : LatticeVertex) (huw : PD.FK.squareLattice.Adj u w)
    (hu : u.2 < v.2 → v.1 ≤ u.1) (hw : w.2 < v.2 → v.1 ≤ w.1) :
    rayStep v u w = (if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0) := by
  have hstep := (squareLattice_adj_iff u w).mp huw
  by_cases hbelow : u.2 < v.2
  · simp only [rayStep,ite_eq_left hbelow,ite_eq_left (hu hbelow),mul_one]
  · by_cases hwbelow : w.2 < v.2
    · have hx : v.1 ≤ u.1 := by have hwx := hw hwbelow; omega
      simp only [rayStep,ite_eq_right hbelow,ite_eq_left hwbelow,ite_eq_left hx,mul_one]
    · simp only [rayStep,ite_eq_right hbelow,ite_eq_right hwbelow,sub_self,zero_mul]

/-- The left-ray telescoping formula needs horizontal bounds ONLY at
vertices strictly below the marker level, where a height crossing can occur. -/
theorem rayIndex_telescope_of_below_left_bound (v : LatticeVertex) {u w : LatticeVertex}
    (p : PD.FK.squareLattice.Walk u w)
    (hleft : ∀ x ∈ p.support, x.2 < v.2 → v.1 ≤ x.1) :
    rayIndex v p = (if u.2 < v.2 then 1 else 0) - (if w.2 < v.2 then 1 else 0) := by
  induction p with
  | nil => simp only [rayIndex,sub_self]
  | @cons u z w h p ih =>
    have hu := hleft u (by simp)
    have hz := hleft z (by simp)
    have ht : ∀ x ∈ p.support, x.2 < v.2 → v.1 ≤ x.1 := by
      intro x hx
      exact hleft x (by simp [hx])
    rw [rayIndex,rayStep_eq_height_difference_of_below_left v u z h hu hz,ih ht]
    omega

private theorem rayStep_zero_of_below_right
    (v u w : LatticeVertex) (huw : PD.FK.squareLattice.Adj u w)
    (hu : u.2 < v.2 → u.1 < v.1) (hw : w.2 < v.2 → w.1 < v.1) :
    rayStep v u w = 0 := by
  have hstep := (squareLattice_adj_iff u w).mp huw
  by_cases hbelow : u.2 < v.2
  · simp only [rayStep,ite_eq_right (not_le_of_gt (hu hbelow)),mul_zero]
  · by_cases hwbelow : w.2 < v.2
    · have hx : u.1 < v.1 := by have hwx := hw hwbelow; omega
      simp only [rayStep,ite_eq_right (not_le_of_gt hx),mul_zero]
    · simp only [rayStep,ite_eq_right hbelow,ite_eq_right hwbelow,sub_self,zero_mul]

/-- No right-ray intersection occurs when every vertex below the marker is
strictly left of it; vertices at higher levels need no horizontal bound. -/
theorem rayIndex_zero_of_below_right_bound (v : LatticeVertex) {u w : LatticeVertex}
    (p : PD.FK.squareLattice.Walk u w)
    (hright : ∀ x ∈ p.support, x.2 < v.2 → x.1 < v.1) : rayIndex v p=0 := by
  induction p with
  | nil => rfl
  | @cons u z w h p ih =>
    have hu := hright u (by simp)
    have hz := hright z (by simp)
    have ht : ∀ x ∈ p.support, x.2 < v.2 → x.1 < v.1 := by
      intro x hx
      exact hright x (by simp [hx])
    rw [rayIndex,rayStep_zero_of_below_right v u z h hu hz,ih ht,zero_add]

end PottsContinuity.Push
