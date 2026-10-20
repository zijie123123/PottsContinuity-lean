module

public import PottsContinuity.Thm3.Push.RectangleCutRestriction
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Literal inclusion of PD rectangle vertices with common bottom and width. -/
theorem rectangle_height_subset (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H) :
    PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle a w H := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  exact ⟨hv.1,hv.2.1,by omega⟩

/-- The corresponding expanded true-dual carriers have the SAME bottom
ports; their top ports need not coincide. -/
theorem rectangle_dual_height_subset (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H) :
    rectangleDualExpanded a w h ⊆ rectangleDualExpanded a w H := by
  intro v hv
  rw [rectangleDualExpanded,mem_latticeRectangle] at hv ⊢
  exact ⟨hv.1,hv.2.1,by omega⟩

/-- The literal expanded-face inclusion preserves every true bottom port. -/
theorem rectangle_dual_height_bottom_port (a : LatticeVertex) (w h H : ℕ) (hle : h ≤ H)
    {v : RectangleDualVertex a w h} (hv : v ∈ rectangleDualBottomPorts a w h) :
    rectangleDualVertexEmbedding (rectangle_dual_height_subset a w h H hle) v ∈
      rectangleDualBottomPorts a w H := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_image.mpr
  refine ⟨i,hi,?_⟩
  apply Subtype.ext
  rfl

end
end PottsContinuity.Push
