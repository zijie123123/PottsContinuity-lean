module

public import PottsContinuity.Thm3.Prop4.TubeStripPhysicalSeparation
public import PottsContinuity.Thm3.Prop4.TubeHalfPlaneEdges

/-!
# Framing the crop inside the physical dual rectangle

The vertex embedding retains exact original face labels. Positive strip
height is directed into the appropriate safe physical half-plane, for either
orientation. No boundary identifications enter these geometric maps.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- The literal framed inclusion of the nested physical crop into the original
finite dual face carrier. -/
def tubeStripPhysicalEmbedding (n N M : ℕ) (t : ℝ) (c : ℤ) (reflected : Bool) :
    (tubeStripPhysicalCrop n N M t c reflected) ↪
      RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) where
  toFun z := ⟨tubeStripFrame c reflected z.val.val,z.property⟩
  inj' := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact (tubeStripFrame c reflected).injective (congrArg Subtype.val h)

/-- A translated or reflected strip rooted at a safe physical height lies
entirely on the required side of the original Euclidean tube. -/
theorem framed_tiltedWindow_safe_height (N M : ℕ) (t b r : ℝ) (c : ℤ) (reflected : Bool)
    (hc : if reflected then (c : ℝ) ≤ b-2*r else b+2*r ≤ (c : ℝ))
    (z : (tiltedWindow N M (if reflected then -t else t) : Set LatticeVertex)) :
    if reflected then tiltedHeight t (tubeStripFrame c reflected z.val) ≤ b-2*r
      else b+2*r ≤ tiltedHeight t (tubeStripFrame c reflected z.val) := by
  have hz := ((mem_tiltedWindow _ _ _ z.val).mp z.property).2.1
  cases reflected <;> dsimp [tiltedStripVertices,tiltedHeight,tubeStripFrame] at hz hc ⊢ <;>
    push_cast <;> linarith only [hz,hc]

end PottsContinuity.Thm3.Prop4
