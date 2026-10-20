-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/JordanOrientation.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.JordanWinding

/-!
# Choosing the positive orientation of a simple closed path

A simple closed path remains simple after reversal, has the same geometric
image, and retains its value at the midpoint. The proved uniform interior
winding sign then selects the original path or its reversal with winding one
at every point of its actual bounded interior. No orientation is assumed,
and no canonical selection is imposed.
-/

@[expose] public section

namespace PottsContinuity.FKC

open Set OAI.SLEExactGauge
open scoped unitInterval

/-- A simple closed path is also injective when the closing endpoint replaces
its starting endpoint in the half-open parameter interval. -/
theorem jordanPath_injOn_Ioc {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) : InjOn γ (Ioc (0 : I) 1) := by
  intro s hs t ht h
  have hzero : (0 : I) ∈ Ico (0 : I) 1 := ⟨le_rfl, zero_lt_one⟩
  have hmem {r : I} (hr : r ≠ 1) : r ∈ Ico (0 : I) 1 :=
    ⟨bot_le, lt_top_iff_ne_top.mpr hr⟩
  by_cases hs1 : s = 1
  · subst s
    by_cases ht1 : t = 1
    · exact ht1.symm
    · have ht0 : t = 0 := hγ (hmem ht1) hzero
        (h.symm.trans (γ.target.trans γ.source.symm))
      exact (ne_of_gt ht.1 ht0).elim
  · by_cases ht1 : t = 1
    · subst t
      have hs0 : s = 0 := hγ (hmem hs1) hzero
        (h.trans (γ.target.trans γ.source.symm))
      exact (ne_of_gt hs.1 hs0).elim
    · exact hγ (hmem hs1) (hmem ht1) h

/-- Reversing a simple closed path preserves injectivity before the closing endpoint. -/
theorem jordanPath_symm_injOn {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) : InjOn γ.symm (Ico (0 : I) 1) := by
  intro s hs t ht h
  have hmem {r : I} (hr : r ∈ Ico (0 : I) 1) : σ r ∈ Ioc (0 : I) 1 := by
    refine ⟨?_, le_top⟩
    simpa only [unitInterval.symm_one] using unitInterval.strictAnti_symm hr.2
  exact unitInterval.symm_inj.mp
    (jordanPath_injOn_Ioc γ hγ (hmem hs) (hmem ht) h)

/-- Time reversal fixes the midpoint parameter, so it preserves the second marked point. -/
theorem path_symm_apply_midpoint {a b : ℂ} (γ : Path a b) (t : I)
    (ht : (t : ℝ) = 1 / 2) : γ.symm t = γ t := by
  have hs : σ t = t := by
    apply Subtype.ext
    simp only [unitInterval.coe_symm_eq, ht]
    norm_num
  change γ (σ t) = γ t
  rw [hs]

/-- One of a simple closed path and its reversal has positive winding throughout
its actual interior, preserving the full image, basepoint, and midpoint mark. -/
theorem exists_positive_jordan_orientation {a : ℂ} (γ : Path a a)
    (hγ : InjOn γ (Ico (0 : I) 1)) :
    ∃ η : Path a a, (η = γ ∨ η = γ.symm) ∧
      InjOn η (Ico (0 : I) 1) ∧ range η = range γ ∧
      (∀ t : I, (t : ℝ) = 1 / 2 → η t = γ t) ∧
      ∀ z (hz : z ∈ complexInside (range η)),
        windingNumber η z (complexInside_subset_complement _ hz) = 1 := by
  rcases windingNumber_jordan_interior_sign γ hγ with hpos | hneg
  · refine ⟨γ, Or.inl rfl, hγ, rfl, ?_, hpos⟩
    intro t _
    rfl
  · refine ⟨γ.symm, Or.inr rfl, jordanPath_symm_injOn γ hγ,
      Path.symm_range γ, path_symm_apply_midpoint γ, ?_⟩
    intro z hz
    have hzγ : z ∈ complexInside (range γ) := by
      rwa [Path.symm_range] at hz
    have h := windingNumber_symm γ z (complexInside_subset_complement _ hzγ)
    simpa only [hneg z hzγ, neg_neg] using h

end PottsContinuity.FKC
