-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanInteriorTransport.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.JordanParametrization
public import PottsContinuity.FKC.SLEWrap.Geometry.ComplexJordanRegions

/-!
# The actual interior under a parametrization-matching plane homeomorphism

The standard circle loop has precisely the unit sphere as its image and the
open unit disk as its bounded interior. A whole-plane homeomorphism matching
that loop with a simple closed path therefore sends the disk onto the actual
bounded interior of the path's image. In particular its image of zero is an
interior point; no interior-point witness is assumed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set Metric OAI.SLEExactGauge
open scoped unitInterval

/-- The actual image of the once-traversed standard circle is the whole unit sphere. -/
theorem range_standardCircleLoop :
    range standardCircleLoop = sphere (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp only [mem_sphere, dist_zero_right, standardCircleLoop_apply, Circle.norm_coe]
  · intro hz
    let z' : Circle := ⟨z, hz⟩
    have hmem : z' ∈ Circle.exp '' Icc 0 (0 + 2 * Real.pi) := by
      rw [Circle.periodic_exp.image_Icc Real.two_pi_pos]
      exact Circle.exp_surjective z'
    obtain ⟨θ, hθ, he⟩ := hmem
    let t : I := ⟨θ / (2 * Real.pi),
      div_nonneg hθ.1 Real.two_pi_pos.le,
      (div_le_one Real.two_pi_pos).mpr (by simpa only [zero_add] using hθ.2)⟩
    refine ⟨t, ?_⟩
    have ht : 2 * Real.pi * (t : ℝ) = θ := by
      dsimp [t]
      field_simp
    rw [standardCircleLoop_apply, ht]
    exact congrArg Subtype.val he

/-- The coordinate image of any simple closed path is a Schoenflies Jordan curve. -/
theorem isJordanCurve_coordinates_range {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    Schoenflies.IsJordanCurve (complexPlaneCoordinates '' range γ) := by
  refine ⟨complexPlaneCoordinates ∘ γ.extend, isLoop_complexCoordinates_extend γ hγ, ?_⟩
  rw [Set.image_comp, γ.image_extend_of_subset (Subset.rfl)]

/-- The bounded interior of the standard circle's actual range is the open unit disk. -/
theorem complexInside_range_standardCircleLoop :
    complexInside (range standardCircleLoop) = ball (0 : ℂ) 1 := by
  apply complexInside_eq_open
    (isJordanCurve_coordinates_range standardCircleLoop standardCircleLoop_injOn)
    isOpen_ball (convex_ball _ _).isPreconnected
    (nonempty_ball.mpr (by norm_num)) isBounded_ball
  rw [frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0), range_standardCircleLoop]

/-- Parameter matching gives equality of the entire curve images. -/
theorem image_range_standardCircleLoop_of_match {a : ℂ} (γ : Path a a)
    (H : ℂ ≃ₜ ℂ) (hH : ∀ t : I, H (standardCircleLoop t) = γ t) :
    H '' range standardCircleLoop = range γ := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hH)

/-- A matching whole-plane homeomorphism sends the entire open disk to the actual interior. -/
theorem image_ball_eq_complexInside_of_match {a : ℂ} (γ : Path a a)
    (H : ℂ ≃ₜ ℂ) (hH : ∀ t : I, H (standardCircleLoop t) = γ t) :
    H '' ball (0 : ℂ) 1 = complexInside (range γ) := by
  rw [← complexInside_range_standardCircleLoop, complexInside_transport,
    image_range_standardCircleLoop_of_match γ H hH]

/-- The image of the disk center supplies a genuine interior point. -/
theorem map_zero_mem_complexInside_of_match {a : ℂ} (γ : Path a a)
    (H : ℂ ≃ₜ ℂ) (hH : ∀ t : I, H (standardCircleLoop t) = γ t) :
    H 0 ∈ complexInside (range γ) := by
  rw [← image_ball_eq_complexInside_of_match γ H hH]
  exact mem_image_of_mem H (by simp)

/-- A simple closed path admits a matching plane homeomorphism that transports the actual
interior and provides an interior point, with no chosen-point assumption. -/
theorem exists_planeHomeomorph_standardCircleLoop_inside {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    ∃ H : ℂ ≃ₜ ℂ, (∀ t : I, H (standardCircleLoop t) = γ t) ∧
      H '' ball (0 : ℂ) 1 = complexInside (range γ) ∧
      H 0 ∈ complexInside (range γ) := by
  obtain ⟨H, hH⟩ := exists_planeHomeomorph_standardCircleLoop γ hγ
  exact ⟨H, hH, image_ball_eq_complexInside_of_match γ H hH,
    map_zero_mem_complexInside_of_match γ H hH⟩

end PottsContinuity.FKC
