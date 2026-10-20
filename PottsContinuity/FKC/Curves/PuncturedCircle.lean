-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/PuncturedCircle.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# The circle action of a punctured plane homeomorphism

The actual inclusion of the unit circle into the punctured complex plane and
the actual radial projection form a homotopy equivalence. Restricting a plane
homeomorphism fixing zero and composing these maps therefore gives a circle
self-homotopy equivalence. Its formula is H(u)/norm(H(u)); no homotopy-inverse
or orientation premise is added to the plane homeomorphism.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set

noncomputable section

/-- The actual complex plane with its origin removed. -/
abbrev PuncturedComplexPlane := ↥((univ : Set ℂ) \ {0})

/-- Inclusion and radial projection are the proved deformation retraction. -/
def circlePuncturedPlaneEquiv :
    ContinuousMap.HomotopyEquiv Circle PuncturedComplexPlane :=
  (starConvex_univ (𝕜 := ℝ) (0 : ℂ)).sphereHomotopyEquiv
    (by norm_num : (0 : ℝ) < 1) (subset_univ _)

/-- A homeomorphism fixing zero restricts to the entire punctured plane. -/
def puncturedPlaneHomeomorph (H : ℂ ≃ₜ ℂ) (hH : H 0 = 0) :
    PuncturedComplexPlane ≃ₜ PuncturedComplexPlane :=
  H.subtype (by
    intro z
    simp only [mem_sdiff, mem_univ, mem_singleton_iff, true_and]
    constructor
    · intro hz h
      exact hz (H.injective (h.trans hH.symm))
    · intro hz h
      subst z
      exact hz hH)

/-- The circle self-map induced by the actual punctured-plane homeomorphism,
including a proved homotopy inverse. -/
def planeHomeomorphCircleEquiv (H : ℂ ≃ₜ ℂ) (hH : H 0 = 0) :
    ContinuousMap.HomotopyEquiv Circle Circle :=
  (circlePuncturedPlaneEquiv.trans (puncturedPlaneHomeomorph H hH).toHomotopyEquiv).trans
    circlePuncturedPlaneEquiv.symm

/-- The forward map is precisely radial projection of the homeomorphic image. -/
theorem planeHomeomorphCircleEquiv_coe_apply (H : ℂ ≃ₜ ℂ) (hH : H 0 = 0)
    (u : Circle) :
    (planeHomeomorphCircleEquiv H hH u : ℂ) = H u / (‖H u‖ : ℂ) := by
  have hu : ((circlePuncturedPlaneEquiv u : PuncturedComplexPlane) : ℂ) = u :=
    StarConvex.coe_sphereHomotopyEquiv_apply _ _ _ u
  have key := StarConvex.coe_sphereHomotopyEquiv_symm_apply (starConvex_univ (𝕜 := ℝ) (0 : ℂ))
    (by norm_num : (0 : ℝ) < 1) (subset_univ _)
    (puncturedPlaneHomeomorph H hH (circlePuncturedPlaneEquiv u))
  have hH' : ((puncturedPlaneHomeomorph H hH (circlePuncturedPlaneEquiv u) :
      PuncturedComplexPlane) : ℂ) = H u := by
    rw [← hu]
    rfl
  refine key.trans ?_
  rw [hH']
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Centering a plane homeomorphism at the image of zero gives one fixing zero. -/
def centeredPlaneHomeomorph (H : ℂ ≃ₜ ℂ) : ℂ ≃ₜ ℂ :=
  H.trans (Homeomorph.addRight (-H 0))

@[simp] theorem centeredPlaneHomeomorph_apply (H : ℂ ≃ₜ ℂ) (z : ℂ) :
    centeredPlaneHomeomorph H z = H z - H 0 := by
  rfl

@[simp] theorem centeredPlaneHomeomorph_zero (H : ℂ ≃ₜ ℂ) :
    centeredPlaneHomeomorph H 0 = 0 := by
  simp

/-- Every plane homeomorphism induces this circle homotopy equivalence about H(0). -/
def centeredCircleEquiv (H : ℂ ≃ₜ ℂ) : ContinuousMap.HomotopyEquiv Circle Circle :=
  planeHomeomorphCircleEquiv (centeredPlaneHomeomorph H) (centeredPlaneHomeomorph_zero H)

theorem centeredCircleEquiv_coe_apply (H : ℂ ≃ₜ ℂ) (u : Circle) :
    (centeredCircleEquiv H u : ℂ) = (H u - H 0) / (‖H u - H 0‖ : ℂ) :=
  planeHomeomorphCircleEquiv_coe_apply _ _ u

end

end PottsContinuity.FKC
