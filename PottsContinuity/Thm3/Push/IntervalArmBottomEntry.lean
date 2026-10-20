module

public import PottsContinuity.Thm3.Push.IntervalArmFaceLabel
public import PottsContinuity.Thm3.Push.BondFaceIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance intervalEntryPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bottom faces strictly before the source interval have the reached label. -/
theorem intervalArmFaceLabel_bottom_before (N : ℕ) (l : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N))
    (v : RectangleVertex (-1,-1) (N+1) (N+1))
    (hy : v.val.2 = -1) (hx : v.val.1 < l) : intervalArmFaceLabel N l A v = true := by
  apply decide_eq_true
  apply intervalArmLeftReached_contains_seed N l A
  exact (mem_intervalArmLeftDualPorts N l _).mpr (Or.inr ⟨hy,hx⟩)

/-- On the original arm event all bottom faces at or after the interval's
right endpoint have the unreached label. -/
theorem intervalArmFaceLabel_bottom_after_of_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    (v : RectangleVertex (-1,-1) (N+1) (N+1))
    (hy : v.val.2 = -1) (hx : r ≤ v.val.1) : intervalArmFaceLabel N l A v = false := by
  apply decide_eq_false
  exact intervalArmLeftReached_avoids_right_of_arm N l r hl hlr hr A p hs ht hsl hsr
    ((mem_intervalArmRightDualPorts N r _).mpr (Or.inr ⟨hy,hx⟩))

/-- Every bottom entry of the second-dual label-cut path returns to an actual
original vertex in the prescribed source interval. The boundary edge cannot
shift the selected starting point outside that interval. -/
theorem intervalArmFaceLabel_bottom_entry_of_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r)
    (i : ℕ) (hi : i < N+1) (z : RectangleDualVertex (-1,-1) (N+1) (N+1))
    (hz : (rectangleLabelCutDualGraph (-1,-1) (N+1) (N+1) (intervalArmFaceLabel N l A)).Adj
      (rectangleDualBottomPortVertex (-1,-1) (N+1) (N+1) i) z) :
    faceIndexMark z.val = ((i : ℤ),0) ∧ l ≤ (i : ℤ) ∧ (i : ℤ) ≤ r := by
  have hstep := (rectangleDualBottomAdj_iff_up_and_flip (-1,-1) (N+1) (N+1)
    (intervalArmFaceLabel N l A) i hi z).mp hz
  have hflip := hstep.2
  rw [rectangleClampedBottomLabel_val _ _ _ _ i hi.le,
    rectangleClampedBottomLabel_val _ _ _ _ (i+1) (by omega)] at hflip
  have hlow : l ≤ (i : ℤ) := by
    by_contra hnot
    have hfirst := intervalArmFaceLabel_bottom_before N l A
      ⟨(-1+(i : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    have hsecond := intervalArmFaceLabel_bottom_before N l A
      ⟨(-1+((i+1 : ℕ) : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    rw [hfirst,hsecond] at hflip
    cases hflip
  have hhigh : (i : ℤ) ≤ r := by
    by_contra hnot
    have hfirst := intervalArmFaceLabel_bottom_after_of_arm N l r hl hlr hr A p hs ht hsl hsr
      ⟨(-1+(i : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    have hsecond := intervalArmFaceLabel_bottom_after_of_arm N l r hl hlr hr A p hs ht hsl hsr
      ⟨(-1+((i+1 : ℕ) : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    rw [hfirst,hsecond] at hflip
    cases hflip
  refine ⟨?_,hlow,hhigh⟩
  rw [hstep.1,rectangleDualBottomUpVertex_val_of_lt _ _ _ i hi]
  simp [faceIndexMark]

end
end PottsContinuity.Push
