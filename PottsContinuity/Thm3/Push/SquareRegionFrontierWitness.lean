module

public import PottsContinuity.Thm3.Push.SquareRegionCellBridge
public import PottsContinuity.Thm3.Push.SquareRegionBottomEntry
public import PottsContinuity.Thm3.Push.LabelCutPathTrim
public import PottsContinuity.Thm3.Push.WalkPullback
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance squareRegionWitnessPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Separating the two prescribed exterior seed arcs by a true-dual region
forces an actual original primal arm from the bottom interval to the full top.
This is a deterministic label-cut theorem with all clipping steps included. -/
theorem squareRegionFrontier_contains_interval_arm
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (S : Set (RectangleDualVertex (0,0) N N))
    (hSLeft : ∀ v ∈ intervalArmLeftDualPorts N l, v ∈ S)
    (hSRight : ∀ v ∈ intervalArmRightDualPorts N r, v ∉ S) :
    ∃ u v : RectangleVertex (0,0) N N,
      u.val.2 = 0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r ∧ v.val.2 = (N : ℤ) ∧
      ActualConnected (rectangleGraph (0,0) N N) (squareRegionFrontier N S) u v := by
  have hleft : ∀ v : RectangleVertex (-1,-1) (N+1) (N+1),
      v.val.1 = -1 → squareRegionFaceLabel N S v = true := by
    intro v hv
    apply decide_eq_true
    exact hSLeft _ ((mem_intervalArmLeftDualPorts N l _).mpr (Or.inl hv))
  have hright : ∀ v : RectangleVertex (-1,-1) (N+1) (N+1),
      v.val.1 = (N : ℤ) → squareRegionFaceLabel N S v = false := by
    intro v hv
    apply decide_eq_false
    exact hSRight _ ((mem_intervalArmRightDualPorts N r _).mpr (Or.inl hv))
  obtain ⟨i,hi,z,q,hentry,hz,hq⟩ := labelCutDual_inner_walk N (by omega)
    (squareRegionFaceLabel N S) hleft hright
  have hstart := squareRegionFaceLabel_bottom_entry N l r S hSLeft hSRight i hi _ hentry
  let j := labelCutDualCellBoundaryHom (-1,-1) (N+1) (N+1) (squareRegionFaceLabel N S)
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
      x ∈ Set.range (squareRegionFrontierCellEmbedding N S) := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact ⟨⟨faceIndexMark y.val,hbox y hy⟩,rfl⟩
  obtain ⟨Q,_⟩ := exists_walk_pullback_support (u := u) (v := v)
    (squareRegionFrontierCellEmbedding N S) P hP
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
