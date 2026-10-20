module

public import PottsContinuity.Thm3.Push.SquareRegionCellBridge
public import PottsContinuity.Thm3.Push.BondFaceIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance squareRegionEntryPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Bottom faces strictly before the source interval have the reached label. -/
theorem squareRegionFaceLabel_bottom_before (N : ℕ) (l : ℤ)
    (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (v : RectangleVertex (-1,-1) (N+1) (N+1))
    (hy : v.val.2 = -1) (hx : v.val.1 < l) : squareRegionFaceLabel N S v = true := by
  apply decide_eq_true
  exact hleft _ ((mem_intervalArmLeftDualPorts N l _).mpr (Or.inr ⟨hy,hx⟩))

/-- All bottom faces at or after the interval's
right endpoint have the unreached label. -/
theorem squareRegionFaceLabel_bottom_after
    (N : ℕ) (r : ℤ) (S : Set (RectangleDualVertex (0,0) N N))
    (hright : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S)
    (v : RectangleVertex (-1,-1) (N+1) (N+1))
    (hy : v.val.2 = -1) (hx : r ≤ v.val.1) : squareRegionFaceLabel N S v = false := by
  apply decide_eq_false
  exact hright _ ((mem_intervalArmRightDualPorts N r _).mpr (Or.inr ⟨hy,hx⟩))

/-- Every bottom entry of the second-dual region-cut path returns to an actual
original vertex in the prescribed source interval. The boundary edge cannot
shift the selected starting point outside that interval. -/
theorem squareRegionFaceLabel_bottom_entry
    (N : ℕ) (l r : ℤ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (hright : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S)
    (i : ℕ) (hi : i < N+1) (z : RectangleDualVertex (-1,-1) (N+1) (N+1))
    (hz : (rectangleLabelCutDualGraph (-1,-1) (N+1) (N+1) (squareRegionFaceLabel N S)).Adj
      (rectangleDualBottomPortVertex (-1,-1) (N+1) (N+1) i) z) :
    faceIndexMark z.val = ((i : ℤ),0) ∧ l ≤ (i : ℤ) ∧ (i : ℤ) ≤ r := by
  have hstep := (rectangleDualBottomAdj_iff_up_and_flip (-1,-1) (N+1) (N+1)
    (squareRegionFaceLabel N S) i hi z).mp hz
  have hflip := hstep.2
  rw [rectangleClampedBottomLabel_val _ _ _ _ i hi.le,
    rectangleClampedBottomLabel_val _ _ _ _ (i+1) (by omega)] at hflip
  have hlow : l ≤ (i : ℤ) := by
    by_contra hnot
    have hfirst := squareRegionFaceLabel_bottom_before N l S hleft
      ⟨(-1+(i : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    have hsecond := squareRegionFaceLabel_bottom_before N l S hleft
      ⟨(-1+((i+1 : ℕ) : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    rw [hfirst,hsecond] at hflip
    cases hflip
  have hhigh : (i : ℤ) ≤ r := by
    by_contra hnot
    have hfirst := squareRegionFaceLabel_bottom_after N r S hright
      ⟨(-1+(i : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    have hsecond := squareRegionFaceLabel_bottom_after N r S hright
      ⟨(-1+((i+1 : ℕ) : ℤ),-1),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
      rfl (by dsimp; omega)
    rw [hfirst,hsecond] at hflip
    cases hflip
  refine ⟨?_,hlow,hhigh⟩
  rw [hstep.1,rectangleDualBottomUpVertex_val_of_lt _ _ _ i hi]
  simp [faceIndexMark]

end
end PottsContinuity.Push
