module

public import PottsContinuity.Thm3.Push.SquareRegionActiveLocality
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- The left exterior cells inherit the literal true-dual side label. -/
theorem squareRegionCells_left_mem (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N))
    (hleft : ∀ v : RectangleDualVertex (0,0) N N, v.val.1 = -1 → v ∈ S)
    (y : ℤ) (hy : -1 ≤ y) (hyN : y ≤ (N : ℤ)) :
    (-1,y) ∈ squareRegionCells N S := by
  let v : RectangleVertex (-1,-1) (N+1) (N+1) :=
    ⟨(-1,y),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  exact (mem_squareRegionCells N S ((squareExpandedFaceEquiv N).symm v)).mpr (hleft _ rfl)

/-- The right exterior cells inherit the opposite true-dual side label. -/
theorem squareRegionCells_right_not_mem (N : ℕ) (S : Set (RectangleDualVertex (0,0) N N))
    (hright : ∀ v : RectangleDualVertex (0,0) N N, v.val.1 = (N : ℤ) → v ∉ S)
    (y : ℤ) (hy : -1 ≤ y) (hyN : y ≤ (N : ℤ)) :
    ((N : ℤ),y) ∉ squareRegionCells N S := by
  let v : RectangleVertex (-1,-1) (N+1) (N+1) :=
    ⟨((N : ℤ),y),by rw [mem_latticeRectangle]; constructor <;> constructor <;> dsimp <;> omega⟩
  exact fun hm => hright _ rfl ((mem_squareRegionCells N S ((squareExpandedFaceEquiv N).symm v)).mp hm)

end
end PottsContinuity.Push
