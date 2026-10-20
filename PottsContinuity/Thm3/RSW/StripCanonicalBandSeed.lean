module

public import PottsContinuity.Thm3.RSW.StripRoundedBandSeed
public import PottsContinuity.Thm3.RSW.StripTranslationArm
public import PottsContinuity.Thm3.RSW.StripArmCaseSplit

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- The segment supplied by the actual union bound transports to the canonical
source interval under the explicit whole-strip translation-law interface. -/
theorem selfDual_strip_canonical_band_seed_of_translationInvariant_and_verticalLower
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hns : n ≤ 9*s)
    (htranslation : ∀ c : ℤ, (selfDualStripMeasure q n).map
      (stripHorizontalTranslationConfiguration n c) = selfDualStripMeasure q n)
    (hvertical : (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    1/(36*(k:ℝ)) ≤ (selfDualStripMeasure q n).real (stripBandArm n (2*n) (4*s) (5*s)) := by
  obtain ⟨j,hj⟩ := selfDual_strip_vertical_has_rounded_band_seed q k n s hk hs hns hvertical
  let a : ℤ := -9*(k:ℤ)*s+(j.val:ℤ)*s
  let b : ℤ := -9*(k:ℤ)*s+((j.val:ℤ)+1)*s
  let c : ℤ := 4*s-a
  have hprob := stripBandArm_real_translation_of_translationInvariant n (2*n) a b c
    (selfDualStripMeasure q n) (htranslation c)
  have hI : a+c = (4*s:ℤ) := by dsimp [c]; ring
  have hJ : b+c = (5*s:ℤ) := by dsimp [a,b,c]; ring
  rw [hI,hJ] at hprob
  rw [hprob]
  exact hj

/-- The source top/left arm dichotomy, including the corrected confined seed,
from explicit strip symmetries and the primal vertical-crossing lower bound. -/
theorem selfDual_strip_source_case_split_of_stripSymmetries_and_verticalLower
    (q : Set.Ici (1:ℝ)) (k n s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hns : n ≤ 9*s)
    (htranslation : ∀ c : ℤ, (selfDualStripMeasure q n).map
      (stripHorizontalTranslationConfiguration n c) = selfDualStripMeasure q n)
    (hreflection : (selfDualStripMeasure q n).map
      (stripHorizontalReflectionConfiguration n (9*s)) = selfDualStripMeasure q n)
    (hvertical : (1/2:ℝ) ≤ (selfDualStripMeasure q n).real
      (stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n))) :
    (1/(36*(k:ℝ)))/3 ≤ (selfDualStripMeasure q n).real
      (stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.2 = 2*n}) ∨
    (1/(36*(k:ℝ)))/3 ≤ (selfDualStripMeasure q n).real
      (stripRectangleArm n 0 (9*s) (2*n) (4*s) (5*s) {v | v.val.1 = 0}) := by
  apply strip_arm_case_split_of_reflectionInvariant n 0 (9*s) (2*n) (4*s) (5*s)
    (by omega) (by omega) (by omega) (selfDualStripMeasure q n) (by simpa only [zero_add] using hreflection)
    (1/(36*(k:ℝ)))
  exact selfDual_strip_canonical_band_seed_of_translationInvariant_and_verticalLower
    q k n s hk hs hns htranslation hvertical

end PottsContinuity.RSW
