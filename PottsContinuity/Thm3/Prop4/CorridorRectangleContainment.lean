module

public import PottsContinuity.Thm3.Prop4.CorridorRectangles

/-!
# Every actual corridor rectangle lies in the Euclidean tube

The horizontal and connector carriers include their complete lattice
boundaries. Inward clamping keeps them inside the original square, and the
proved center margin places every sampled vertex in the literal tube.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- All horizontal stage vertices belong to the actual original-lattice tube. -/
theorem corridorHorizontalVertices_subset_radiusTube {n : ℕ} (hn : 1 ≤ n)
    (s : ℕ) (hs : s ≤ n) (u v : ℤ × ℤ) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (R : ℝ) (hR : 4*(s : ℝ)+1 ≤ R) (i : ℕ) :
    corridorHorizontalVertices n s hs t b i ⊆ radiusTube n R u v := by
  intro z hz
  have hzB := corridorHorizontalVertices_subset_box n s hs t b i hz
  have hmem := hz
  rw [corridorHorizontalVertices,PD.FK.mem_latticeRectangle] at hmem
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hmem
  apply corridor_point_mem_radiusTube hn s hs u v huB hvB ha hb t b ht hu hv
    (corridorAbscissa n s i+(s : ℤ)) (corridor_midpoint_bounds n s hs i) z hzB ?_ ?_ R hR
  · rw [abs_le]
    omega
  · change |z.2-corridorCenter n s hs t b i| ≤ 2*(s : ℤ)
    rw [abs_le]
    omega

/-- All overlap connector vertices belong to the same actual tube. -/
theorem corridorConnectorVertices_subset_radiusTube {n : ℕ} (hn : 1 ≤ n)
    (s : ℕ) (hs : s ≤ n) (u v : ℤ × ℤ) (huB : u ∈ box n) (hvB : v ∈ box n)
    (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b) (R : ℝ) (hR : 4*(s : ℝ)+1 ≤ R) (i : ℕ) :
    corridorConnectorVertices n s hs t b i ⊆ radiusTube n R u v := by
  intro z hz
  have hzB := corridorConnectorVertices_subset_box n s hs t b i hz
  have hx := corridorAbscissa_step n s i
  have hy := corridorCenter_step n s hs t b ht i
  rw [abs_le] at hy
  have hmem := hz
  rw [corridorConnectorVertices,PD.FK.mem_latticeRectangle] at hmem
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_natAbs] at hmem
  apply corridor_point_mem_radiusTube hn s hs u v huB hvB ha hb t b ht hu hv
    (corridorAbscissa n s i+(s : ℤ)) (corridor_midpoint_bounds n s hs i) z hzB ?_ ?_ R hR
  · rw [abs_le]
    omega
  · change |z.2-corridorCenter n s hs t b i| ≤ 2*(s : ℤ)
    rw [abs_le]
    simp only [abs_eq_max_neg] at hmem
    omega

end PottsContinuity.Thm3.Prop4
