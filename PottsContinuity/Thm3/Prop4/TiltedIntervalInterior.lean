module

public import PottsContinuity.Thm3.Prop4.TiltedStoppedInterval

/-! # Interior geometry for the actual scanned tilted interval -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The strip height bounds the vertical absolute coordinate by |x|+n,
for all slopes in the source range. -/
theorem tiltedStrip_abs_y_le (n : ℕ) (t : ℝ) (ht : |t| ≤ 1) (z : ℤ × ℤ)
    (hz : z ∈ tiltedStripVertices n t) : |z.2| ≤ |z.1|+(n : ℤ) := by
  have hmul : |t*(z.1 : ℝ)| ≤ |(z.1 : ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) ht
  have hp := abs_le.mp hmul
  have hz' : 0 ≤ (z.2 : ℝ)-t*z.1 ∧ (z.2 : ℝ)-t*z.1 ≤ n := hz
  have hy : |(z.2 : ℝ)| ≤ |(z.1 : ℝ)|+(n : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hp.1,hp.2,hz'.1,hz'.2]
  exact_mod_cast hy

/-- Columns strictly within the two horizontal margins give vertices strictly
inside the outer square, including at tilted supporting-line vertices. -/
theorem tiltedInterval_avoids_boxBoundary (n M : ℕ) (t : ℝ) (ht : |t| ≤ 1) (lo hi : ℤ)
    (hlo : -(M : ℤ)+(n : ℤ) < lo) (hhi : hi < (M : ℤ)-(n : ℤ)) :
    ∀ z ∈ tiltedInterval n M t lo hi, z ∉ vertexBoundary (box M) := by
  intro z hz hb
  have hzint := (mem_tiltedInterval n M t lo hi z).mp hz
  have hzstrip := ((mem_tiltedWindow n M t z).mp hzint.1).2
  have hy := tiltedStrip_abs_y_le n t ht z hzstrip
  have hx : |z.1|+(n : ℤ) < M := by simp only [abs_eq_max_neg]; omega
  rw [Foundations.vertexBoundary_box_eq] at hb
  change max |z.1| |z.2| = (M : ℤ) at hb
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  omega

/-- The chosen outer-to-inner scan starts automatically satisfy the geometric
premise of the exact stopped interval law, for every successful pair of hits. -/
theorem scanned_tiltedInterval_avoids_boxBoundary (n M : ℕ) (t : ℝ) (ht : |t| ≤ 1)
    (i j : ℕ) :
    ∀ z ∈ tiltedInterval n M t (-(M : ℤ)+n+i+1) ((M : ℤ)-n-1-j),
      z ∉ vertexBoundary (box M) := by
  apply tiltedInterval_avoids_boxBoundary n M t ht
  · omega
  · omega

/-- Successful scan intervals contain the requested central columns when
K cuts are scanned on each side of those columns. -/
theorem scanned_tiltedInterval_contains_center (n M R K : ℕ)
    (hscale : M = n+R+K) (i j : ℕ) (hi : i < K) (hj : j < K)
    (t : ℝ) (z : ℤ × ℤ) (hz : z ∈ tiltedWindow n M t) (hx : |z.1| ≤ (R : ℤ)) :
    z ∈ tiltedInterval n M t (-(M : ℤ)+n+i+1) ((M : ℤ)-n-1-j) := by
  apply (mem_tiltedInterval _ _ _ _ _ _).mpr
  have hscaleZ : (M : ℤ) = n+R+K := by exact_mod_cast hscale
  have hx' := abs_le.mp hx
  exact ⟨hz,by omega,by omega⟩

end PottsContinuity.Thm3.Prop4
