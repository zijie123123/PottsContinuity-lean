module

public import PottsContinuity.Thm3.Prop4.CapsuleSupportingFunctional
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# A genuine nearest-point normal for a maximal Euclidean excursion

Compactness supplies a nearest segment point. The convex projection
characterization gives its variational inequality and hence the supporting
half-plane for the complete capsule, including both endpoint caps.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Every point has an actual nearest segment point with its variational
support inequality. No selection function is introduced. -/
theorem exists_segment_nearest_normal (u v z : ℂ) :
    ∃ p ∈ segment ℝ u v, Metric.infDist z (segment ℝ u v) = ‖z-p‖ ∧
      ∀ y ∈ segment ℝ u v, (star (z-p)*(y-p)).re ≤ 0 := by
  have hcompact : IsCompact (segment ℝ u v) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨p,hp,hd⟩ := hcompact.exists_infDist_eq_dist ⟨u,left_mem_segment ℝ _ _⟩ z
  rw [dist_eq_norm] at hd
  have hi : ‖z-p‖ = ⨅ y : segment ℝ u v, ‖z-y.val‖ := by
    rw [← hd,Metric.infDist_eq_iInf]
    simp only [dist_eq_norm]
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_segment u v) hp).mp hi
  refine ⟨p,hp,hd,?_⟩
  intro y hy
  have hh := hvar y hy
  rw [real_inner_eq_re_inner ℂ,RCLike.inner_apply'] at hh
  exact hh

end PottsContinuity.Thm3.Prop4
