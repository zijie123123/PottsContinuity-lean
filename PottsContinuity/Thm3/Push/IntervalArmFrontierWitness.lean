module

public import PottsContinuity.Thm3.Push.IntervalArmCellBridge
public import PottsContinuity.Thm3.Push.IntervalArmBottomEntry
public import PottsContinuity.Thm3.Push.LabelCutPathTrim
public import PottsContinuity.Thm3.Push.WalkPullback
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- On the actual source interval-to-top event, the canonical left frontier
itself contains an actual arm with the SAME permitted starting interval.
All path existence, true-dual separation, boundary clipping and original-edge
transport are discharged. -/
theorem intervalArmLeftFrontier_contains_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N))
    {s t : RectangleVertex (0,0) N N}
    (p : (openGraph (rectangleGraph (0,0) N N) A).Walk s t)
    (hs : s.val.2 = 0) (ht : t.val.2 = (N : ℤ))
    (hsl : l ≤ s.val.1) (hsr : s.val.1 ≤ r) :
    ∃ u v : RectangleVertex (0,0) N N,
      u.val.2 = 0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r ∧ v.val.2 = (N : ℤ) ∧
      ActualConnected (rectangleGraph (0,0) N N) (intervalArmLeftFrontier N l A) u v := by
  have hleft := intervalArmFaceLabel_left N l A
  have hright := intervalArmFaceLabel_right_of_arm N l r hl hlr hr A p hs ht hsl hsr
  obtain ⟨i,hi,z,q,hentry,hz,hq⟩ := labelCutDual_inner_walk N (by omega)
    (intervalArmFaceLabel N l A) hleft hright
  have hstart := intervalArmFaceLabel_bottom_entry_of_arm N l r hl hlr hr A p
    hs ht hsl hsr i hi _ hentry
  let j := labelCutDualCellBoundaryHom (-1,-1) (N+1) (N+1) (intervalArmFaceLabel N l A)
  let P := q.map j
  have hbox : ∀ v ∈ q.support, faceIndexMark v.val ∈ latticeRectangle (0,0) N N := by
    intro v hv
    have h := hq v hv
    rw [mem_latticeRectangle]
    simp only [faceIndexMark,zero_add]
    constructor <;> constructor <;> omega
  let u : RectangleVertex (0,0) N N :=
    ⟨faceIndexMark (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i).val,
      hbox _ q.start_mem_support⟩
  let v : RectangleVertex (0,0) N N := ⟨faceIndexMark z.val,hbox _ q.end_mem_support⟩
  have hP : ∀ x ∈ P.support,
      x ∈ Set.range (intervalArmLeftFrontierCellEmbedding N l A) := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨faceIndexMark y.val,hbox y hy⟩,rfl⟩
  obtain ⟨Q,_⟩ := exists_walk_pullback_support (u := u) (v := v)
    (intervalArmLeftFrontierCellEmbedding N l A) P hP
  refine ⟨u,v,?_,?_,?_,?_,⟨Q⟩⟩
  · change (faceIndexMark (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i).val).2 = 0
    rw [hstart.1]
  · change l ≤ (faceIndexMark (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i).val).1
    rw [hstart.1]
    exact hstart.2.1
  · change (faceIndexMark (rectangleDualBottomUpVertex (-1,-1) (N+1) (N+1) i).val).1 ≤ r
    rw [hstart.1]
    exact hstart.2.2
  · change z.val.2+1 = (N : ℤ)
    omega

end
end PottsContinuity.Push
