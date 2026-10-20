-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/WindingRegions.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Winding number on complementary regions

The degree of the actual radial projection of a continuous closed complex path
is unchanged as its center moves along any path avoiding the loop's image.
Consequently it is constant on each path component of the complement, and on
each connected open region contained in the complement. No regularity beyond
continuity is required, and no Jordan interior value is asserted here.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set
open scoped unitInterval

/-- Moving the center along a path avoiding the loop does not change winding number. -/
theorem windingNumber_eq_of_path {a z₀ z₁ : ℂ} (γ : Path a a)
    (hz₀ : z₀ ∉ range γ) (hz₁ : z₁ ∉ range γ)
    (p : Path z₀ z₁) (hp : ∀ s, p s ∉ range γ) :
    windingNumber γ z₀ hz₀ = windingNumber γ z₁ hz₁ := by
  have havoid (u : I × I) : γ u.2 - p u.1 ≠ 0 :=
    sub_ne_zero.mpr (fun h => hp u.1 ⟨u.2, h⟩)
  let G : C(I × I, Circle) :=
    ⟨fun u => radialProjection 0 ⟨γ u.2 - p u.1, havoid u⟩,
      (continuous_radialProjection 0).comp
        (((γ.continuous.comp continuous_snd).sub
          (p.continuous.comp continuous_fst)).subtype_mk havoid)⟩
  apply Circle.degree_eq_of_homotopy (normalizedLoop γ z₀ hz₀)
    (normalizedLoop γ z₁ hz₁) G
  · intro t
    apply Subtype.ext
    change ((γ t - p 0) - 0) / (‖(γ t - p 0) - 0‖ : ℂ) =
      (γ t - z₀) / (‖γ t - z₀‖ : ℂ)
    rw [p.source, sub_zero]
  · intro t
    apply Subtype.ext
    change ((γ t - p 1) - 0) / (‖(γ t - p 1) - 0‖ : ℂ) =
      (γ t - z₁) / (‖γ t - z₁‖ : ℂ)
    rw [p.target, sub_zero]
  · intro s
    apply congrArg (radialProjection 0)
    apply Subtype.ext
    change γ 0 - p s = γ 1 - p s
    rw [γ.source, γ.target]

/-- Points joined inside the complement have the same winding number. -/
theorem windingNumber_eq_of_joinedIn {a z₀ z₁ : ℂ} (γ : Path a a)
    (hz₀ : z₀ ∉ range γ) (hz₁ : z₁ ∉ range γ)
    (h : JoinedIn (range γ)ᶜ z₀ z₁) :
    windingNumber γ z₀ hz₀ = windingNumber γ z₁ hz₁ := by
  obtain ⟨p, hp⟩ := h
  exact windingNumber_eq_of_path γ hz₀ hz₁ p hp

/-- Winding number is constant on every path-connected region avoiding the loop. -/
theorem windingNumber_eq_on_isPathConnected {a : ℂ} (γ : Path a a)
    {U : Set ℂ} (hU : IsPathConnected U) (havoid : U ⊆ (range γ)ᶜ)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U) :
    windingNumber γ z₀ (havoid hz₀) = windingNumber γ z₁ (havoid hz₁) :=
  windingNumber_eq_of_joinedIn γ (havoid hz₀) (havoid hz₁)
    ((hU.joinedIn z₀ hz₀ z₁ hz₁).mono havoid)

/-- Every connected open complementary region has a single winding-number value. -/
theorem windingNumber_eq_on_isOpen_isConnected {a : ℂ} (γ : Path a a)
    {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsConnected U)
    (havoid : U ⊆ (range γ)ᶜ) {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U) :
    windingNumber γ z₀ (havoid hz₀) = windingNumber γ z₁ (havoid hz₁) :=
  windingNumber_eq_on_isPathConnected γ
    (hUopen.isConnected_iff_isPathConnected.mp hUconn) havoid hz₀ hz₁

end PottsContinuity.FKC
