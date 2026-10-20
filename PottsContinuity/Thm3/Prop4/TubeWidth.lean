module

public import PottsContinuity.Thm3.Prop4.TubePartition

/-!
# A uniform literal width bound for Lemma 7's tube

A coarse factor 2 replaces the source's sharp √2. This suffices for the
finite-energy exponential cost and keeps all integer-rounding cases explicit.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every point of an endpoint segment lies on the same affine supporting line. -/
theorem tube_segment_on_line (u v : ℤ × ℤ) (t b : ℝ)
    (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b)
    {w : ℂ} (hw : w ∈ segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) :
    w.im = t*w.re+b := by
  rcases hw with ⟨a,c,ha,hc,hac,rfl⟩
  simp only [Complex.add_im, Complex.add_re, Complex.smul_im, Complex.smul_re,
    smul_eq_mul]
  change a*(u.2 : ℝ)+c*(v.2 : ℝ) = t*(a*(u.1 : ℝ)+c*(v.1 : ℝ))+b
  rw [hu,hv]
  linear_combination b*hac

/-- Euclidean radius r implies vertical deviation <2r at slopes of absolute value ≤1. -/
theorem tube_vertical_deviation_lt (u v z : ℤ × ℤ) (t b r : ℝ)
    (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*(u.1 : ℝ)+b)
    (hv : (v.2 : ℝ) = t*(v.1 : ℝ)+b)
    (hz : tubeDistance u v z < r) :
    |(z.2 : ℝ)-(t*(z.1 : ℝ)+b)| < 2*r := by
  obtain ⟨w,hw,hd⟩ := (Metric.infDist_lt_iff
    ⟨tubeLatticePoint u, left_mem_segment ℝ _ _⟩).mp hz
  rw [dist_eq_norm] at hd
  have hx : |(z.1 : ℝ)-w.re| < r := by
    exact (Complex.abs_re_le_norm (tubeLatticePoint z-w)).trans_lt hd
  have hy : |(z.2 : ℝ)-w.im| < r := by
    exact (Complex.abs_im_le_norm (tubeLatticePoint z-w)).trans_lt hd
  have hwline := tube_segment_on_line u v t b hu hv hw
  calc
    |(z.2 : ℝ)-(t*(z.1 : ℝ)+b)| =
        |((z.2 : ℝ)-w.im)-t*((z.1 : ℝ)-w.re)| := by rw [hwline]; ring_nf
    _ ≤ |(z.2 : ℝ)-w.im|+|t*((z.1 : ℝ)-w.re)| := abs_sub _ _
    _ = |(z.2 : ℝ)-w.im|+|t| * |(z.1 : ℝ)-w.re| := by rw [abs_mul]
    _ ≤ |(z.2 : ℝ)-w.im|+|(z.1 : ℝ)-w.re| := by
      apply add_le_add le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht
        (abs_nonneg ((z.1 : ℝ)-w.re))
    _ < 2*r := by linarith only [hx,hy]

end PottsContinuity.Thm3.Prop4
