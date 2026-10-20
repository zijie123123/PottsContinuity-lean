module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Thm3.RSW.TiltedReducedMarginal
public import PottsContinuity.Thm3.Touch.ReducedMarginalComposition
public import PottsContinuity.Assembly.NearFinal

/-!
# Proof of `PottsContinuity.theorem_3`

This module proves `PottsContinuity.Provider.theorem_3`, whose statement is exactly that of
`theorem_3` in `Frozen/Theorem3.lean` (with an implicit `q` and an auto-param `hq`), from the
other project modules. The proof in `Frozen/Theorem3.lean` is `by exact` this theorem; no other
module imports this one.

Proof assembly: Lemma 6 (the hypothesis `hTouch` of `Assembly.theorem_3_of_touch`, with the
corrected coefficient 1/(20 k² l²)) is obtained from the tilted-strip reduced-carrier self-duality
`RSW.selfDual_tiltedStrip_reflected_marginal` through
`Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal` (which uses the
half-height bound `PlanarMixed.TiltedHalfHeight.selfDualTiltedHalfHeight_ge_half`);
`Assembly.theorem_3_of_touch` discharges every other link.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.Provider

open PottsContinuity

/-- Lemma 6 at the explicit self-dual parameter, with the corrected coefficient 1/(20 k² l²). -/
theorem touch_lower_bound (q : Set.Ici (1:ℝ)) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l)
    (s : ℝ) (hs : s ∈ Set.Icc (-1:ℝ) 1) :
    1 / (20 * (k:ℝ) ^ 2 * (l:ℝ) ^ 2) ≤
      Thm3.Prop4.tiltedTouchProbability (RSW.selfDualParameters q) k l s :=
  Thm3.Touch.selfDual_tilted_touch_all_slopes_corrected_of_reducedMarginal q k l hk hkl
    (fun s' hs' => RSW.selfDual_tiltedStrip_reflected_marginal q (2*k) s' hs') s hs

/-- Exactly the statement of `PottsContinuity.theorem_3`, with an implicit `q` and an auto-param
`hq`, so that its proof in `Frozen/Theorem3.lean` is `by exact` this theorem. -/
theorem theorem_3 {q : ℝ} (hq : 1 ≤ q := by assumption) :
    ∃ (pc : Set.Icc (0 : ℝ) 1) (φ : Fin 2 → Measure (squareLattice.edgeSet → Bool)),
      IsRCCriticalPoint ⟨q, hq⟩ pc ∧
      (∀ i, IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq⟩ i (φ i)) ∧
      List.TFAE
        [ φ 1 {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0,
          φ 0 = φ 1,
          ∑' x : ℤ × ℤ, φ 0 {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ∞,
          Tendsto
            (fun n : ℕ => 1 / (n : ℝ) * Real.log ((φ 0).real
              {ω | ∃ y ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
            atTop (𝓝 0),
          ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
            c ≤ rcEventProb
              (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
              pc ⟨q, lt_of_lt_of_le one_pos hq⟩ 0
              (horizontalCrossing
                (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n))
                0 ⌊α * n⌋ 0 n)] :=
  Assembly.theorem_3_of_touch q hq touch_lower_bound

end PottsContinuity.Provider
