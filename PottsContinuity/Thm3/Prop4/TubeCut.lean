module

public import PottsContinuity.Thm3.Prop4.TubeWidth
public import PottsContinuity.Thm3.Prop4.TiltedCandidates

/-!
# The literal central cut of the tube

The source cut at x=1/2 consists of the horizontal edges (0,y)--(1,y)
whose two endpoints belong to D. We first index these edges by their unique
integer rows. The uniform size bound includes all integer rounding terms.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every pair of genuine opposite-face endpoints has an admissible supporting line. -/
theorem inductionTube_supporting_line {n : ℕ} (hn : 1 ≤ n)
    (u v : ℤ × ℤ) (hu : u ∈ box n) (hv : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = (n : ℤ)) :
    ∃ t b : ℝ, |t| ≤ 1 ∧
      (u.2 : ℝ) = t*(u.1 : ℝ)+b ∧ (v.2 : ℝ) = t*(v.1 : ℝ)+b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huY : -(n : ℤ) ≤ u.2 ∧ u.2 ≤ (n : ℤ) := by
    have h := hu
    simp only [box, Finset.mem_product, Finset.mem_Icc] at h
    exact h.2
  have hvY : -(n : ℤ) ≤ v.2 ∧ v.2 ≤ (n : ℤ) := by
    have h := hv
    simp only [box, Finset.mem_product, Finset.mem_Icc] at h
    exact h.2
  have huL : -(n : ℝ) ≤ (u.2 : ℝ) := by exact_mod_cast huY.1
  have huU : (u.2 : ℝ) ≤ n := by exact_mod_cast huY.2
  have hvL : -(n : ℝ) ≤ (v.2 : ℝ) := by exact_mod_cast hvY.1
  have hvU : (v.2 : ℝ) ≤ n := by exact_mod_cast hvY.2
  refine ⟨((v.2 : ℝ)-(u.2 : ℝ))/(2*n), ((u.2 : ℝ)+(v.2 : ℝ))/2, ?_, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · apply (le_div_iff₀ (by positivity)).mpr
      linarith only [huU,hvL]
    · apply (div_le_iff₀ (by positivity)).mpr
      linarith only [hvU,huL]
  · rw [huX]
    push_cast
    field_simp
    ring
  · rw [hvX]
    push_cast
    field_simp
    ring

end PottsContinuity.Thm3.Prop4
