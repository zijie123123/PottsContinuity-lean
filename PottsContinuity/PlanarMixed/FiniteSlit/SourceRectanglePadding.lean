module

public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleClipping
public import PottsContinuity.Thm3.RSW.FiniteSlitInterior

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- The original rectangle is contained in the padded source square. -/
theorem rectangle_subset_paddedSquare (w h : ℕ) :
    PD.FK.latticeRectangle (0,0) w h ⊆
      PD.FK.latticeRectangle (0,0) (2*(w+h)) (2*(w+h)) := by
  intro z hz
  rw [PD.FK.mem_latticeRectangle] at hz ⊢
  dsimp at hz ⊢
  omega

/-- Literal inclusion into a padded square, used only to construct finite
crosscuts. No configuration or FK law is placed on this auxiliary square. -/
def rectangleToPaddedSquare (w h : ℕ) :
    RectangleVertex (0,0) w h ↪ RectangleVertex (0,0) (2*(w+h)) (2*(w+h)) :=
  Set.embeddingOfSubset _ _ (rectangle_subset_paddedSquare w h)

/-- Canonical reference inclusion of an arbitrary source rectangle, with
padding strictly outside all three non-bottom source sides. -/
def paddedRectangleReference (w h : ℕ) (x : ℤ) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ)) :
    RectangleVertex (0,0) w h ↪ Vertex (2*(w+h)+2) x :=
  rectangleIntoReference (2*(w+h)+2) x w h (by omega) (by omega) (by omega) (by omega)

/-- Both stages of deterministic padding preserve the original coordinates. -/
theorem paddedSquare_reference_comp (w h : ℕ) (x : ℤ) (hx : 1 ≤ x)
    (hxw : x ≤ (w:ℤ)) (v : RectangleVertex (0,0) w h) :
    sourceSquareSlitEmbedding (w+h) x (by omega) (by omega)
      (rectangleToPaddedSquare w h v) = paddedRectangleReference w h x hx hxw v :=
  Subtype.ext rfl

end
end PottsContinuity.PlanarMixed.FiniteSlit
