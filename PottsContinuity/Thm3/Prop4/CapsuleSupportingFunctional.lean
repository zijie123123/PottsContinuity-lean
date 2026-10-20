module

public import PottsContinuity.Thm3.Prop4.TubeGeometry

/-!
# A normal supporting the segment also supports its Euclidean capsule

The normal is anchored at a nearest-point variational inequality, rather
than assumed parallel to the original endpoint chord. This is the corrected
geometric route for a maximal Euclidean excursion.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- A variational supporting normal of the segment bounds every point within
the excursion radius, including points whose closest point is an endpoint. -/
theorem capsule_supporting_functional_le_of_segment_normal (u v z p w : ℂ)
    (hnormal : ∀ y ∈ segment ℝ u v, (star (z-p)*(y-p)).re ≤ 0)
    (hw : Metric.infDist w (segment ℝ u v) ≤ ‖z-p‖) :
    (star (z-p)*(w-p)).re ≤ ‖z-p‖^2 := by
  have hcompact : IsCompact (segment ℝ u v) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨y,hy,hd⟩ := hcompact.exists_infDist_eq_dist
    ⟨u,left_mem_segment ℝ _ _⟩ w
  have hwy : ‖w-y‖ ≤ ‖z-p‖ := by
    rw [← dist_eq_norm,← hd]
    exact hw
  have hcs : (star (z-p)*(w-y)).re ≤ ‖z-p‖*‖w-y‖ := by
    calc
      _ ≤ |(star (z-p)*(w-y)).re| := le_abs_self _
      _ ≤ ‖star (z-p)*(w-y)‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul,norm_star]
  calc
    _ = (star (z-p)*(w-y)).re+(star (z-p)*(y-p)).re := by
      rw [← Complex.add_re,← mul_add]
      congr 1
      ring
    _ ≤ ‖z-p‖*‖w-y‖+0 := add_le_add hcs (hnormal y hy)
    _ ≤ ‖z-p‖^2 := by
      rw [add_zero,pow_two]
      exact mul_le_mul_of_nonneg_left hwy (norm_nonneg _)


/-- The normal at a variational nearest point gives a supporting half-plane
for every point no farther from the segment than the selected excursion. -/
theorem capsule_normal_half_plane_of_maximal_distance (u v z p w : ℂ)
    (hnormal : ∀ y ∈ segment ℝ u v, (star (z-p)*(y-p)).re ≤ 0)
    (hz : Metric.infDist z (segment ℝ u v) = ‖z-p‖)
    (hw : Metric.infDist w (segment ℝ u v) ≤ Metric.infDist z (segment ℝ u v)) :
    (star (z-p)*(w-z)).re ≤ 0 := by
  have hcap : Metric.infDist w (segment ℝ u v) ≤ ‖z-p‖ := hw.trans_eq hz
  have hbound := capsule_supporting_functional_le_of_segment_normal u v z p w hnormal hcap
  have hself : (star (z-p)*(z-p)).re = ‖z-p‖^2 := by
    have hh := congrArg Complex.re (Complex.conj_mul' (z-p))
    simpa only [Complex.star_def,← Complex.ofReal_pow,Complex.ofReal_re] using hh
  have hsplit : (star (z-p)*(w-p)).re =
      (star (z-p)*(w-z)).re+(star (z-p)*(z-p)).re := by
    rw [← Complex.add_re,← mul_add]
    congr 1
    ring
  rw [hsplit,hself] at hbound
  linarith only [hbound]

end PottsContinuity.Thm3.Prop4
