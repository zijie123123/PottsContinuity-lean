-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/Winding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import TauCeti.Topology.Circle.Degree

/-!
# Winding numbers of continuous complex loops

The winding number is the degree of the actual radial projection about a point
outside the loop's image. The projection is defined on the punctured plane, so
there is no value assigned at its excluded center. No smoothness, rectifiability,
or constant-speed parametrization is required.

This file proves reversal and homotopy properties. That the winding number has
one sign, plus or minus one, throughout the interior of a Jordan loop is proved in
`FKC.Domains.JordanWinding` (`windingNumber_jordan_interior_sign`); counterclockwise
orientation is then defined as winding one on the interior
(`MarkedBoundaryParametrization.counterclockwise`).
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set
open scoped unitInterval

noncomputable section

/-- Radial projection to the unit circle, defined only away from its center. -/
def radialProjection (z : ℂ) (w : {w : ℂ // w ≠ z}) : Circle :=
  ⟨(w.val - z) / (‖w.val - z‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr w.property))]⟩

@[simp] theorem radialProjection_coe (z : ℂ) (w : {w : ℂ // w ≠ z}) :
    (radialProjection z w : ℂ) = (w.val - z) / (‖w.val - z‖ : ℂ) := rfl

theorem continuous_radialProjection (z : ℂ) : Continuous (radialProjection z) := by
  apply Continuous.subtype_mk
  have h : Continuous (fun w : {w : ℂ // w ≠ z} => w.val - z) :=
    continuous_subtype_val.sub continuous_const
  exact h.div (Complex.continuous_ofReal.comp h.norm) (fun w =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr w.property)))

/-- The basepoint of a loop avoids every point outside its image. -/
theorem basepoint_ne_of_not_mem_range {a z : ℂ} (γ : Path a a)
    (hz : z ∉ range γ) : a ≠ z := fun h => hz ⟨0, γ.source.trans h⟩

/-- A continuous loop about an omitted point, radially projected to the circle. -/
def normalizedLoop {a : ℂ} (γ : Path a a) (z : ℂ) (hz : z ∉ range γ) :
    Path (radialProjection z ⟨a, basepoint_ne_of_not_mem_range γ hz⟩)
      (radialProjection z ⟨a, basepoint_ne_of_not_mem_range γ hz⟩) where
  toFun t := radialProjection z ⟨γ t, fun h => hz ⟨t, h⟩⟩
  continuous_toFun := (continuous_radialProjection z).comp
    (γ.continuous.subtype_mk (fun t h => hz ⟨t, h⟩))
  source' := by congr 1; exact Subtype.ext γ.source
  target' := by congr 1; exact Subtype.ext γ.target

@[simp] theorem normalizedLoop_coe_apply {a : ℂ} (γ : Path a a) (z : ℂ)
    (hz : z ∉ range γ) (t : I) :
    (normalizedLoop γ z hz t : ℂ) = (γ t - z) / (‖γ t - z‖ : ℂ) := rfl

/-- The integer winding number of a continuous loop about a point outside its image. -/
def windingNumber {a : ℂ} (γ : Path a a) (z : ℂ) (hz : z ∉ range γ) : ℤ :=
  Circle.degree (normalizedLoop γ z hz)

/-- Reversal preserves the omitted-point condition. -/
theorem not_mem_range_symm {a z : ℂ} (γ : Path a a) (hz : z ∉ range γ) :
    z ∉ range γ.symm := by rwa [Path.symm_range]

/-- Radial projection commutes with reversal of a loop. -/
theorem normalizedLoop_symm {a : ℂ} (γ : Path a a) (z : ℂ) (hz : z ∉ range γ) :
    normalizedLoop γ.symm z (not_mem_range_symm γ hz) = (normalizedLoop γ z hz).symm := by
  ext t
  rfl

/-- Reversing a continuous loop negates its winding number. -/
theorem windingNumber_symm {a : ℂ} (γ : Path a a) (z : ℂ) (hz : z ∉ range γ) :
    windingNumber γ.symm z (not_mem_range_symm γ hz) = -windingNumber γ z hz := by
  rw [windingNumber, normalizedLoop_symm, Circle.degree_symm, windingNumber]

/-- A constant loop misses every different point. -/
theorem not_mem_range_refl {a z : ℂ} (haz : a ≠ z) : z ∉ range (Path.refl a) := by
  rintro ⟨t, h⟩
  exact haz h

/-- Radially projecting a constant loop gives the constant circle loop. -/
theorem normalizedLoop_refl (a z : ℂ) (haz : a ≠ z) :
    normalizedLoop (Path.refl a) z (not_mem_range_refl haz) =
      Path.refl (radialProjection z ⟨a, haz⟩) := by
  ext t
  rfl

/-- Every constant loop has zero winding number about each point it avoids. -/
theorem windingNumber_refl (a z : ℂ) (haz : a ≠ z) :
    windingNumber (Path.refl a) z (not_mem_range_refl haz) = 0 := by
  rw [windingNumber, normalizedLoop_refl a z haz, Circle.degree_refl]

/-- Winding number is invariant under a continuous free homotopy of loops
whose entire image avoids the specified point. The basepoint may move. -/
theorem windingNumber_eq_of_homotopy {a b : ℂ}
    (γ₀ : Path a a) (γ₁ : Path b b) (z : ℂ)
    (hz₀ : z ∉ range γ₀) (hz₁ : z ∉ range γ₁)
    (F : C(I × I, ℂ))
    (h₀ : ∀ t, F (0, t) = γ₀ t) (h₁ : ∀ t, F (1, t) = γ₁ t)
    (hF : ∀ s, F (s, 0) = F (s, 1)) (hzF : ∀ u, F u ≠ z) :
    windingNumber γ₀ z hz₀ = windingNumber γ₁ z hz₁ := by
  let G : C(I × I, Circle) :=
    ⟨fun u => radialProjection z ⟨F u, hzF u⟩,
      (continuous_radialProjection z).comp (F.continuous.subtype_mk hzF)⟩
  apply Circle.degree_eq_of_homotopy (normalizedLoop γ₀ z hz₀)
    (normalizedLoop γ₁ z hz₁) G
  · intro t
    apply congrArg (radialProjection z)
    exact Subtype.ext (h₀ t)
  · intro t
    apply congrArg (radialProjection z)
    exact Subtype.ext (h₁ t)
  · intro s
    apply congrArg (radialProjection z)
    exact Subtype.ext (hF s)

end

end PottsContinuity.FKC
