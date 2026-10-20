module

public import PottsContinuity.Thm3.Push.BaseCrossingTransport
public import PottsContinuity.Thm3.RSW.StripEventLimit
public import PottsContinuity.Thm3.RSW.WalkClipping

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
open MeasureTheory Filter Topology
noncomputable section

/-- The finite top-only strip window is dominated by the source three-side
wired base law, for the actual horizontal crossing at scale 3*s. -/
theorem stripWindow_crossing_probability_le_base (θ : Parameters) (k : ℝ) (s M : ℕ)
    (hM : ⌊k*(3*s : ℕ)⌋ ≤ (M : ℤ)) :
    stripWindowEventProbability θ s M
      (stripHorizontalCrossing s (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (2*s)) ≤
    finiteBoundaryEventProbability (topWiredRectangle k (4/3) (3*s)) θ
      (topWiredRectangleBoundary k (4/3) (3*s))
      (horizontalCrossing (topWiredRectangle k (4/3) (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ)) := by
  let S := finiteBoolEvent (topWiredRectangle k (4/3) (3*s))
    (horizontalCrossing (topWiredRectangle k (4/3) (3*s))
      (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ))
  have hS : IsUpperSet S := finiteBoolEvent_isUpperSet _ _
    (horizontalCrossing_isUpperSet _ _ _ _ _)
  have hcompare := baseStripWindow_restriction_probability_le θ k s M hM S hS
  apply le_trans _ hcompare
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact fun C hC => strip_crossing_implies_base_restricted_crossing k s M hM C hC

/-- Literal strip comparison at every scale divisible by three, with no
RSW estimate assumed. The probability on the left is the constructed strip
law, not an infinite-domain DMP postulate. -/
theorem selfDual_strip_probability_le_base_at_three_mul
    (q : Set.Ici (1 : ℝ)) (k : ℝ) (s : ℕ) :
    selfDualStripHorizontalProbability q (3*k) s ≤
      selfDualTopWiredCrossingProbability q k (4/3) (3*s) := by
  have heq : (3*k)*s = k*(3*s : ℕ) := by push_cast; ring
  unfold selfDualStripHorizontalProbability
  rw [heq]
  apply le_of_tendsto_of_tendsto
    (stripWindowEventProbability_tendsto (selfDualParameters q) s
      (selfDualStripMeasure q s) (selfDualStripMeasure_isLimit q s) _
      (stripHorizontalCrossing_isClopen _ _ _ _ _)) tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌊k*(3*s : ℕ)⌋.natAbs] with M hM
  apply stripWindow_crossing_probability_le_base
  exact le_trans (Int.le_natAbs (a := ⌊k*(3*s : ℕ)⌋)) (by exact_mod_cast hM)

/-- Lemma 2 implies the uniform base bound on divisible scales. The sole
external premise is the explicitly authorized source Lemma-2 conclusion.
No height comparison or highest-crossing product estimate is assumed. -/
theorem selfDual_base_at_three_mul_of_stripRSW
    (q : Set.Ici (1 : ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (k : ℝ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualTopWiredCrossingProbability q k (4/3) (3*s) := by
  obtain ⟨c, hc, hbound⟩ := hstrip (max 1 (3*k)) (le_max_left _ _)
  refine ⟨c, hc, fun s hs => (hbound s hs).trans ?_⟩
  exact (selfDualStripHorizontalProbability_antitone q s (by linarith only [hk])
    (le_max_right _ _)).trans (selfDual_strip_probability_le_base_at_three_mul q k s)

end
end PottsContinuity.Push
