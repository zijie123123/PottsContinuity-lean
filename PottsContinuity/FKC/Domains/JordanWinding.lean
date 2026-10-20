-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanWinding.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.CircleDegreeEquivalence
public import PottsContinuity.FKC.Curves.PuncturedCircle
public import PottsContinuity.FKC.Curves.WindingRegions
public import PottsContinuity.FKC.Domains.JordanInteriorTransport
public import PottsContinuity.FKC.Domains.JordanInside

/-!
# The winding number in the actual interior of a Jordan loop

A parametrization-matching plane homeomorphism supplies an actual interior
point. Its induced circle map is a homotopy equivalence, so the winding number
there is plus or minus one. Constancy throughout the connected open Jordan
interior gives one uniform sign for all interior points. No orientation,
regularity, or interior-degree assertion is assumed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

/-- The actual bounded complementary region is disjoint from the curve itself. -/
theorem complexInside_subset_complement (C : Set ℂ) : complexInside C ⊆ Cᶜ := by
  intro z hz hC
  exact Schoenflies.inside_subset_compl hz (mem_image_of_mem complexPlaneCoordinates hC)

/-- The radial winding of a matched Jordan path at H(0) is the degree of the
actual circle homotopy equivalence induced by H. -/
theorem windingNumber_eq_circleMapDegree_of_match {a : ℂ} (γ : Path a a)
    (H : ℂ ≃ₜ ℂ) (hH : ∀ t : I, H (standardCircleLoop t) = γ t)
    (hz : H 0 ∉ range γ) :
    windingNumber γ (H 0) hz = circleMapDegree (centeredCircleEquiv H).toFun := by
  apply circleDegree_eq_of_pointwise_eq
  intro t
  apply Subtype.ext
  change (γ t - H 0) / (‖γ t - H 0‖ : ℂ) =
    (centeredCircleEquiv H (standardCirclePath t) : ℂ)
  rw [centeredCircleEquiv_coe_apply]
  change (γ t - H 0) / (‖γ t - H 0‖ : ℂ) =
    (H (standardCircleLoop t) - H 0) / (‖H (standardCircleLoop t) - H 0‖ : ℂ)
  rw [hH t]

/-- A simple closed continuous path has a single winding sign on its entire
bounded interior, and that sign is exactly plus or minus one. -/
theorem windingNumber_jordan_interior_sign {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    (∀ z (hz : z ∈ complexInside (range γ)),
      windingNumber γ z (complexInside_subset_complement _ hz) = 1) ∨
    (∀ z (hz : z ∈ complexInside (range γ)),
      windingNumber γ z (complexInside_subset_complement _ hz) = -1) := by
  obtain ⟨H, hH, -, hzero⟩ := exists_planeHomeomorph_standardCircleLoop_inside γ hγ
  have hJ := isJordanCurve_coordinates_range γ hγ
  have heq (z : ℂ) (hz : z ∈ complexInside (range γ)) :
      windingNumber γ (H 0) (complexInside_subset_complement _ hzero) =
        windingNumber γ z (complexInside_subset_complement _ hz) :=
    windingNumber_eq_on_isOpen_isConnected γ (isOpen_complexInside hJ)
      (isConnected_complexInside hJ) (complexInside_subset_complement _) hzero hz
  have hsign :
      windingNumber γ (H 0) (complexInside_subset_complement _ hzero) = 1 ∨
      windingNumber γ (H 0) (complexInside_subset_complement _ hzero) = -1 := by
    rw [windingNumber_eq_circleMapDegree_of_match γ H hH]
    exact circleMapDegree_homotopyEquiv (centeredCircleEquiv H)
  rcases hsign with h | h
  · exact Or.inl (fun z hz => (heq z hz).symm.trans h)
  · exact Or.inr (fun z hz => (heq z hz).symm.trans h)

end PottsContinuity.FKC
