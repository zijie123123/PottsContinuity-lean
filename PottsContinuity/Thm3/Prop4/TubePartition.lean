module

public import PottsContinuity.Thm3.Prop4.TubeGeometry

/-!
# The three genuine regions of Lemma 7

For endpoints on opposite vertical faces, every collinear square vertex lies
on the endpoint segment. Thus the Euclidean tube and the two signed outside
regions partition the actual original lattice square, for every endpoint parity.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- There is no extension-of-the-segment ambiguity inside the square. -/
theorem tube_segment_of_offset_zero {n : ℕ} (hn : 1 ≤ n)
    (u v z : ℤ × ℤ) (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    (hz : z ∈ box n) (hoff : tubeLineOffset u v z = 0) :
    tubeLatticePoint z ∈ segment ℝ (tubeLatticePoint u) (tubeLatticePoint v) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hzX : -(n : ℤ) ≤ z.1 ∧ z.1 ≤ (n : ℤ) := by
    have h := hz
    simp only [box, Finset.mem_product, Finset.mem_Icc] at h
    exact h.1
  have hzL : -(n : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast hzX.1
  have hzU : (z.1 : ℝ) ≤ n := by exact_mod_cast hzX.2
  have hline : ((n : ℝ)+(n : ℝ))*((z.2 : ℝ)-(u.2 : ℝ)) -
      ((v.2 : ℝ)-(u.2 : ℝ))*((z.1 : ℝ)+(n : ℝ)) = 0 := by
    have h : ((v.1 : ℝ)-(u.1 : ℝ))*((z.2 : ℝ)-(u.2 : ℝ)) -
        ((v.2 : ℝ)-(u.2 : ℝ))*((z.1 : ℝ)-(u.1 : ℝ)) = 0 := by
      exact_mod_cast hoff
    simpa [hu, hv] using h
  refine ⟨((n : ℝ)-(z.1 : ℝ))/(2*n), ((z.1 : ℝ)+(n : ℝ))/(2*n),
    div_nonneg (sub_nonneg.mpr hzU) (by positivity),
    div_nonneg (by linarith only [hzL]) (by positivity), ?_, ?_⟩
  · field_simp
    ring
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      change (((n : ℝ)-(z.1 : ℝ))/(2*n))*(u.1 : ℝ) +
        (((z.1 : ℝ)+(n : ℝ))/(2*n))*(v.1 : ℝ) = (z.1 : ℝ)
      rw [hu, hv]
      push_cast
      field_simp
      ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      change (((n : ℝ)-(z.1 : ℝ))/(2*n))*(u.2 : ℝ) +
        (((z.1 : ℝ)+(n : ℝ))/(2*n))*(v.2 : ℝ) = (z.2 : ℝ)
      field_simp
      nlinarith only [hline]

/-- Every original square vertex belongs to exactly one of the three source regions. -/
theorem inductionTube_three_region_cover {n : ℕ} (hn : 1 ≤ n) (ε : ℝ)
    (u v : ℤ × ℤ) (hu : u.1 = -(n : ℤ)) (hv : v.1 = (n : ℤ))
    {z : ℤ × ℤ} (hz : z ∈ box n) :
    z ∈ inductionTube n ε u v ∨ z ∈ inductionTubeBelow n ε u v ∨
      z ∈ inductionTubeAbove n ε u v := by
  classical
  by_cases ht : z ∈ inductionTube n ε u v
  · exact Or.inl ht
  · have hne : tubeLineOffset u v z ≠ 0 := by
      intro heq
      exact ht (inductionTube_mem_of_segment hn ε u v z hz
        (tube_segment_of_offset_zero hn u v z hu hv hz heq))
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hz, ht, hneg⟩))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hz, ht, hpos⟩))

end PottsContinuity.Thm3.Prop4
