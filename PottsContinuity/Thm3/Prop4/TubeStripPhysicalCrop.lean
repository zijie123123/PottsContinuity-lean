module

public import PottsContinuity.Thm3.Prop4.TiltedGeometry
public import PottsContinuity.PD.Duality.RectangleDualAmbient

/-!
# The literal physical crop of a translated or reflected tilted window

The frame has vertical origin c. Reflection sends positive strip height
downwards. The crop retains exactly the vertices in the physical expanded
dual rectangle, and its separator is the genuine exterior face layer.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- A vertical translate, with optional vertical reflection, on the whole lattice. -/
def tubeStripFrame (c : ℤ) (reflected : Bool) : squareLattice ≃g squareLattice where
  toFun z := (z.1,if reflected then c-z.2 else c+z.2)
  invFun z := (z.1,if reflected then c-z.2 else z.2-c)
  left_inv := by intro z; cases reflected <;> ext <;> simp
  right_inv := by intro z; cases reflected <;> ext <;> simp
  map_rel_iff' := by
    intro z w
    change |z.1-w.1|+|((if reflected then c-z.2 else c+z.2) : ℤ)-
      (if reflected then c-w.2 else c+w.2)|=1 ↔ |z.1-w.1|+|z.2-w.2|=1
    cases reflected
    · change |z.1-w.1|+|(c+z.2)-(c+w.2)|=1 ↔ _
      rw [add_sub_add_left_eq_sub]
    · change |z.1-w.1|+|(c-z.2)-(c-w.2)|=1 ↔ _
      rw [sub_sub_sub_cancel_left,abs_sub_comm w.2 z.2]

/-- The finite strip vertices whose framed coordinates lie in the original
physical expanded dual box. This is an exact intersection on the whole carrier. -/
def tubeStripPhysicalCrop (n N M : ℕ) (t : ℝ) (c : ℤ) (reflected : Bool) :
    Set (tiltedWindow N M t : Set LatticeVertex) :=
  {z | tubeStripFrame c reflected z.val ∈ rectangleDualExpanded (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}

/-- The physical exterior face layer, on that same cropped finite strip carrier. -/
def tubeStripPhysicalSeparator (n N M : ℕ) (t : ℝ) (c : ℤ) (reflected : Bool) :
    Set (tiltedWindow N M t : Set LatticeVertex) :=
  {z | tubeStripFrame c reflected z.val ∈ rectangleDualBoundary (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)}

/-- Every physical separator vertex is a vertex of the crop. -/
theorem tubeStripPhysicalSeparator_subset_crop (n N M : ℕ) (t : ℝ) (c : ℤ) (reflected : Bool) :
    tubeStripPhysicalSeparator n N M t c reflected ⊆ tubeStripPhysicalCrop n N M t c reflected := by
  intro z hz
  exact (Finset.mem_filter.mp hz).1

/-- Framing a physical point back into the strip gives uniform coordinate
bounds, for either orientation and every permitted vertical root. -/
theorem tubeStripPhysicalCrop_coordinate_bounds (n N M : ℕ) (t : ℝ)
    (c : ℤ) (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) (reflected : Bool)
    (z : (tiltedWindow N M t : Set LatticeVertex))
    (hz : z ∈ tubeStripPhysicalCrop n N M t c reflected) :
    |z.val.1| ≤ (n : ℤ)+1 ∧ |z.val.2| ≤ 2*(n : ℤ)+1 := by
  change tubeStripFrame c reflected z.val ∈ rectangleDualExpanded _ _ _ at hz
  rw [rectangleDualExpanded,mem_latticeRectangle] at hz
  cases reflected <;> dsimp [tubeStripFrame] at hz<;>
    rw [abs_le,abs_le] <;> omega

end PottsContinuity.Thm3.Prop4
