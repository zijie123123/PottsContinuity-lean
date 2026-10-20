module

public import PottsContinuity.Thm3.Touch.FiniteStripSymmetry
public import PottsContinuity.PD.Duality.Rectangle

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open PottsContinuity.PD.FK
open PottsContinuity.Thm3.Prop4

/-- The column-truncated strip maps into a rectangle with margin supplied by
the strip height and the slope bound. -/
def tiltedColumnRectangleVertexMap (n L : ℕ) (t : ℝ) :
    (tiltedColumnWindow (2*n) L t : Set (ℤ × ℤ)) →
      RectangleVertex (-(L + 2*n + 2 : ℕ), -(L + 2*n + 2 : ℕ))
        (2*(L + 2*n + 2)) (2*(L + 2*n + 2)) := fun z => ⟨z.1, by
    have hzbox : z.1 ∈ box (L + 2*n + 2) := by
      have hz : z.1 ∈ tiltedColumnWindow (2*n) L t := Finset.mem_coe.mp z.2
      simp only [tiltedColumnWindow, Finset.mem_filter, mem_tiltedWindow] at hz
      exact hz.1.1
    have hxy := (Foundations.mem_box_iff_abs_le (L + 2*n + 2) z.1).mp hzbox
    rw [mem_latticeRectangle]
    rcases abs_le.mp hxy.1 with ⟨hxlo, hxhi⟩
    rcases abs_le.mp hxy.2 with ⟨hylo, hyhi⟩
    push_cast
    constructor
    · exact ⟨hxlo, by omega⟩
    · exact ⟨hylo, by omega⟩⟩

/-- The coordinate map is injective and preserves the induced lattice edges. -/
def tiltedColumnRectangleEmbedding (n L : ℕ) (t : ℝ) :
    (tiltedColumnWindow (2*n) L t : Set (ℤ × ℤ)) ↪
      RectangleVertex (-(L + 2*n + 2 : ℕ), -(L + 2*n + 2 : ℕ))
        (2*(L + 2*n + 2)) (2*(L + 2*n + 2)) where
  toFun := tiltedColumnRectangleVertexMap n L t
  inj' := by
    intro x y h
    apply Subtype.ext
    simpa [tiltedColumnRectangleVertexMap] using congrArg Subtype.val h

/-- The embedded column graph is a subgraph of its bounding rectangle. -/
theorem tiltedColumnGraph_map_le_boundingRectangle (n L : ℕ) (t : ℝ) :
    (tiltedColumnGraph (2*n) L t).map
        (tiltedColumnRectangleEmbedding n L t) ≤
      rectangleGraph (-(L + 2*n + 2 : ℕ), -(L + 2*n + 2 : ℕ))
        (2*(L + 2*n + 2)) (2*(L + 2*n + 2)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  change squareLattice.Adj u.1 v.1 at huv
  change squareLattice.Adj
    (tiltedColumnRectangleEmbedding n L t u).1
    (tiltedColumnRectangleEmbedding n L t v).1
  change squareLattice.Adj
    (tiltedColumnRectangleVertexMap n L t u).1
    (tiltedColumnRectangleVertexMap n L t v).1
  dsimp [tiltedColumnRectangleVertexMap]
  exact huv

end PottsContinuity.Thm3.Touch
