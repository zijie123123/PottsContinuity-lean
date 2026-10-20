-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/WindingHalfPlane.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Curves

open Set
open scoped unitInterval
noncomputable section

/-- A loop contained in a convex set which omits `z` contracts linearly inside
that set, so its actual winding number about `z` vanishes. -/
theorem windingNumber_eq_zero_of_range_subset_convex {a z : ℂ}
    (γ : Path a a) (D : Set ℂ) (hD : Convex ℝ D)
    (hrange : Set.range γ ⊆ D) (hz : z ∉ D) :
    windingNumber γ z (fun h => hz (hrange h)) = 0 := by
  have haD : a ∈ D := hrange ⟨0, by simp⟩
  have hne : a ≠ z := fun h => hz (h ▸ haD)
  let F : ContinuousMap (I × I) ℂ := {
    toFun := fun u => AffineMap.lineMap (γ u.2) a (u.1 : ℝ)
    continuous_toFun := by fun_prop
  }
  have hzF : ∀ u : I × I, F u ≠ z := by
    intro u hu
    have hmem : F u ∈ D := by
      simpa [F] using hD.lineMap_mem (hrange ⟨u.2, rfl⟩) haD
        (show (u.1 : ℝ) ∈ Set.Icc (0:ℝ) 1 from u.1.2)
    exact hz (by simpa [hu] using hmem)
  have hwind := windingNumber_eq_of_homotopy γ (Path.refl a) z
    (fun h => hz (hrange h)) (not_mem_range_refl hne) F
    (by intro t; simp [F])
    (by intro t; simp [F])
    (by intro s; simp [F])
    hzF
  rw [hwind, windingNumber_refl a z hne]

/-- If a loop lies strictly to the left of a vertical line, its winding is zero
about every point on or to the right of that line. -/
theorem windingNumber_eq_zero_of_range_re_lt {a z : ℂ}
    (γ : Path a a) (c : ℝ)
    (hγ : ∀ t, (γ t).re < c) (hz : c ≤ z.re) :
    windingNumber γ z (by
      intro h
      rcases h with ⟨t, rfl⟩
      exact (not_lt_of_ge hz) (hγ t)) = 0 := by
  apply windingNumber_eq_zero_of_range_subset_convex γ {w | w.re < c}
    (convex_halfSpace_lt Complex.reLm.isLinear c)
  · intro w hw
    rcases hw with ⟨t, rfl⟩
    exact hγ t
  · exact not_lt_of_ge hz

/-- If a loop lies strictly to the right of a vertical line, its winding is zero
about every point on or to the left of that line. -/
theorem windingNumber_eq_zero_of_range_re_gt {a z : ℂ}
    (γ : Path a a) (c : ℝ)
    (hγ : ∀ t, c < (γ t).re) (hz : z.re ≤ c) :
    windingNumber γ z (by
      intro h
      rcases h with ⟨t, rfl⟩
      exact (not_lt_of_ge hz) (hγ t)) = 0 := by
  apply windingNumber_eq_zero_of_range_subset_convex γ {w | c < w.re}
    (convex_halfSpace_gt Complex.reLm.isLinear c)
  · intro w hw
    rcases hw with ⟨t, rfl⟩
    exact hγ t
  · exact not_lt_of_ge hz

/-- If a loop lies strictly below a horizontal line, its winding is zero about
every point on or above that line. -/
theorem windingNumber_eq_zero_of_range_im_lt {a z : ℂ}
    (γ : Path a a) (c : ℝ)
    (hγ : ∀ t, (γ t).im < c) (hz : c ≤ z.im) :
    windingNumber γ z (by
      intro h
      rcases h with ⟨t, rfl⟩
      exact (not_lt_of_ge hz) (hγ t)) = 0 := by
  apply windingNumber_eq_zero_of_range_subset_convex γ {w | w.im < c}
    (convex_halfSpace_lt Complex.imLm.isLinear c)
  · intro w hw
    rcases hw with ⟨t, rfl⟩
    exact hγ t
  · exact not_lt_of_ge hz

end
end PottsContinuity.FKC.Curves
