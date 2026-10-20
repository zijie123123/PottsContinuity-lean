module

public import PottsContinuity.Thm3.RSW.StripCrossingPositive

/-! # Uniform positive strip crossing bounds on a finite set of scales -/

@[expose] public section

namespace PottsContinuity.RSW

/-- Each fixed finite range has one common positive crossing bound.
The witness may depend on the range; no all-scale RSW conclusion is inferred. -/
theorem selfDual_strip_crossing_finite_scales_uniform_pos
    (q : Set.Ici (1:ℝ)) (k : ℝ) (hk : 0 ≤ k) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, n ≤ N →
      c ≤ selfDualStripHorizontalProbability q k n := by
  let S := Finset.range (N+1)
  have hS : S.Nonempty := ⟨0,by simp [S]⟩
  refine ⟨S.inf' hS (selfDualStripHorizontalProbability q k),?_,?_⟩
  · apply (Finset.lt_inf'_iff hS).mpr
    intro n _
    exact selfDualStripHorizontalProbability_pos q k hk n
  · intro n hn
    exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- Ceiling spacing gives a positive integral arc length at every positive
scale, while its chain span covers n. -/
theorem strip_ceil_ninth_spacing (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ (n+8)/9 ∧ n ≤ 9*((n+8)/9) ∧ 9*((n+8)/9) < n+9 := by
  omega

end PottsContinuity.RSW
