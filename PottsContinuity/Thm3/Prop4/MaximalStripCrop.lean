module

public import PottsContinuity.Thm3.Prop4.TubeStripPhysicalCrop

/-!
# A physical dual crop rooted at an arbitrary lattice face

Translation uses both coordinates of the actual maximal vertex. The crop
and its target are literal inverse images of the physical expanded rectangle
and its exterior face layer.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- The exact physical crop of the strip translated to its actual root. -/
def maximalStripCrop (n N M : ℕ) (t : ℝ) (z : LatticeVertex) :
    Set (tiltedWindow N M t : Set LatticeVertex) :=
  {w | latticeTranslate z w.val ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}

/-- The true physical face boundary, before any original bonds are revealed. -/
def maximalStripSeparator (n N M : ℕ) (t : ℝ) (z : LatticeVertex) :
    Set (tiltedWindow N M t : Set LatticeVertex) :=
  {w | latticeTranslate z w.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}

/-- Every actual separator face lies in the physical crop. -/
theorem maximalStripSeparator_subset_crop (n N M : ℕ) (t : ℝ) (z : LatticeVertex) :
    maximalStripSeparator n N M t z ⊆ maximalStripCrop n N M t z := by
  intro w hw
  exact (Finset.mem_filter.mp hw).1

/-- The original strip origin maps to the prescribed root. -/
theorem tiltedWindowOrigin_mem_maximalStripCrop (n N M : ℕ) (t : ℝ) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    tiltedWindowOrigin N M t ∈ maximalStripCrop n N M t z := by
  change latticeTranslate z (0,0) ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
  simpa only [latticeTranslate,zero_add] using hz

/-- Translation adds the root's tilted height exactly. -/
theorem latticeTranslate_tiltedHeight (t : ℝ) (z w : LatticeVertex) :
    tiltedHeight t (latticeTranslate z w) = tiltedHeight t z + tiltedHeight t w := by
  dsimp [tiltedHeight,latticeTranslate]
  push_cast
  ring

/-- The entire translated strip is above the line through its root. -/
theorem maximalStrip_height_ge_root (N M : ℕ) (t : ℝ) (z : LatticeVertex)
    (w : (tiltedWindow N M t : Set LatticeVertex)) :
    tiltedHeight t z ≤ tiltedHeight t (latticeTranslate z w.val) := by
  rw [latticeTranslate_tiltedHeight]
  exact le_add_of_nonneg_right ((mem_tiltedWindow N M t w.val).mp w.property).2.1

/-- Both local coordinates of a cropped vertex differ from the physical
root by at most the actual side length plus one. -/
theorem maximalStripCrop_coordinate_bounds (n N M : ℕ) (t : ℝ) (z : LatticeVertex)
    (hz : z ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
    (w : (tiltedWindow N M t : Set LatticeVertex)) (hw : w ∈ maximalStripCrop n N M t z) :
    |w.val.1| ≤ 2*(n : ℤ)+1 ∧ |w.val.2| ≤ 2*(n : ℤ)+1 := by
  change latticeTranslate z w.val ∈ rectangleDualExpanded _ _ _ at hw
  rw [rectangleDualExpanded,mem_latticeRectangle] at hz hw
  dsimp [latticeTranslate] at hz hw
  constructor <;> apply abs_le.mpr <;> constructor <;> omega

/-- A lattice translation embeds the cropped strip into physical face labels. -/
def maximalStripEmbedding (n N M : ℕ) (t : ℝ) (z : LatticeVertex) :
    maximalStripCrop n N M t z ↪ RectangleDualVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) where
  toFun w := ⟨latticeTranslate z w.val.val,w.property⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (latticeTranslationIso z).injective (congrArg Subtype.val hab)

end PottsContinuity.Thm3.Prop4
