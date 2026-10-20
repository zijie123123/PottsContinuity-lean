module

public import PottsContinuity.Thm3.RSW.WalkChain
public import PottsContinuity.Thm3.RSW.StripRSWConditional

/-!
# Deterministic source gluing from the interlaced-path interface

This module reduces the actual translated-event inclusion to the basic planar
intersection statement for paths with alternating bottom endpoints. All chain
joining, coordinate arithmetic, and clipping to the target rectangle are proved.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Integer-aspect estimates imply real-aspect estimates along the same scale
sequence. The lower constant is taken at a larger integer aspect; clipping
proves the event inclusion with the original floor convention. -/
theorem selfDual_stripRSW_real_aspect_of_integer_aspects
    (q : Set.Ici (1 : ℝ)) (N : ℕ → ℕ)
    (hinteger : ∀ K : ℕ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j →
      c ≤ selfDualStripHorizontalProbability q K (N j))
    (k : ℝ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j →
      c ≤ selfDualStripHorizontalProbability q k (N j) := by
  let K := ⌈k⌉₊ + 1
  have hK : 1 ≤ K := by omega
  have hkK : k ≤ (K : ℝ) := by
    have h := Nat.le_ceil k
    dsimp [K]
    push_cast
    linarith
  obtain ⟨c, hc, hbound⟩ := hinteger K hK
  exact ⟨c, hc, fun j hj => le_trans (hbound j hj)
    (selfDualStripHorizontalProbability_antitone q (N j) (by linarith) hkK)⟩

end PottsContinuity.RSW
