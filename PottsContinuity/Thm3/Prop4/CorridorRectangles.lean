module

public import PottsContinuity.Thm3.Prop4.CorridorAbscissas
public import PottsContinuity.Thm3.Prop4.CorridorTubeContainment
public import PottsContinuity.PD.Duality.Rectangle

/-!
# Actual rectangles forming the digital sloped corridor

Horizontal rectangles have side 2s. The connector at consecutive anchors has
width s and extends vertically across both rows of the adjacent rectangles.
All carriers are genuine closed induced lattice rectangles inside the box.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The rounded inward center at the midpoint of a horizontal stage. -/
noncomputable def corridorCenter (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (i : ℕ) : ℤ :=
  corridorRow n s hs t b (corridorAbscissa n s i+(s : ℤ))

/-- Original vertices of the horizontal crossing rectangle at a stage. -/
noncomputable def corridorHorizontalVertices (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (i : ℕ) :
    Finset (ℤ × ℤ) :=
  PD.FK.latticeRectangle (corridorAbscissa n s i,corridorCenter n s hs t b i-(s : ℤ)) (2*s) (2*s)

/-- Original vertices of the vertical overlap connector. -/
noncomputable def corridorConnectorVertices (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (i : ℕ) :
    Finset (ℤ × ℤ) :=
  PD.FK.latticeRectangle
    (corridorAbscissa n s (i+1),min (corridorCenter n s hs t b i) (corridorCenter n s hs t b (i+1))-(s : ℤ))
    s (2*s+(corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i).natAbs)

/-- Each midpoint lies over the actual endpoint segment's abscissa interval. -/
theorem corridor_midpoint_bounds (n s : ℕ) (hs : s ≤ n) (i : ℕ) :
    -(n : ℤ) ≤ corridorAbscissa n s i+(s : ℤ) ∧ corridorAbscissa n s i+(s : ℤ) ≤ n := by
  have h := corridorAbscissa_bounds n s hs i
  omega

/-- The integer center rows have a unit-slope step bound along the actual capped anchors. -/
theorem corridorCenter_step (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (ht : |t| ≤ 1) (i : ℕ) :
    |corridorCenter n s hs t b (i+1)-corridorCenter n s hs t b i| ≤ (s : ℤ) := by
  have hx := corridorAbscissa_step n s i
  apply corridorRow_step n s hs t b ht _ _ s
  rw [abs_le]
  omega

/-- Every horizontal rectangle is contained in the original square. -/
theorem corridorHorizontalVertices_subset_box (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (i : ℕ) :
    corridorHorizontalVertices n s hs t b i ⊆ box n := by
  intro z hz
  have hx := corridorAbscissa_bounds n s hs i
  have hy := corridorRow_bounds n s hs t b (corridorAbscissa n s i+(s : ℤ))
  change -(n : ℤ)+(s : ℤ) ≤ corridorCenter n s hs t b i ∧
    corridorCenter n s hs t b i ≤ (n : ℤ)-(s : ℤ) at hy
  rw [corridorHorizontalVertices,PD.FK.mem_latticeRectangle] at hz
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hz
  simp only [box,Finset.mem_product,Finset.mem_Icc]
  omega

/-- Every connector stays in the original square, including when centers are clamped at its sides. -/
theorem corridorConnectorVertices_subset_box (n s : ℕ) (hs : s ≤ n) (t b : ℝ) (i : ℕ) :
    corridorConnectorVertices n s hs t b i ⊆ box n := by
  intro z hz
  have hx := corridorAbscissa_bounds n s hs (i+1)
  have hy := corridorRow_bounds n s hs t b (corridorAbscissa n s i+(s : ℤ))
  have hy' := corridorRow_bounds n s hs t b (corridorAbscissa n s (i+1)+(s : ℤ))
  change -(n : ℤ)+(s : ℤ) ≤ corridorCenter n s hs t b i ∧
    corridorCenter n s hs t b i ≤ (n : ℤ)-(s : ℤ) at hy
  change -(n : ℤ)+(s : ℤ) ≤ corridorCenter n s hs t b (i+1) ∧
    corridorCenter n s hs t b (i+1) ≤ (n : ℤ)-(s : ℤ) at hy'
  rw [corridorConnectorVertices,PD.FK.mem_latticeRectangle] at hz
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs] at hz
  simp only [box,Finset.mem_product,Finset.mem_Icc]
  simp only [abs_eq_max_neg] at hz
  omega

end PottsContinuity.Thm3.Prop4
