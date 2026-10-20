module

public import PottsContinuity.Thm3.Push.StripSourceTranslation
public import PottsContinuity.Thm3.Push.StripCaseTwoArmPreparation

@[expose] public section

namespace PottsContinuity.Push

/-- A single reference placement of the printed Case 2 alternative supplies
both required arm bounds at EVERY translated gluing placement. -/
theorem selfDual_strip_case_two_arm_bounds_all_offsets_of_left
    (q : Set.Ici (1 : ℝ)) (n s : ℕ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (hleft : c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripSourceSquareEvent n 0
      (sourceSquareSideArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0))) :
    ∀ x : ℤ,
      c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x) ∧
      c₁/6 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoSecondArm n s x) := by
  intro x
  apply selfDual_strip_case_two_arm_bounds_of_left q n s x hscale c₁
  have heq := strip_limit_sourceSquareEvent_translation (RSW.selfDualParameters q) n _
    (RSW.selfDualStripMeasure_isLimit q n) 0 x
    (sourceSquareSideArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0)
    (sourceSquareSideArmEvent_isUpperSet _ _ _ _ _ _)
  rw [heq] at hleft
  simpa only [zero_add] using hleft

/-- The rounded Case 2 marginal preparation is uniform over all offsets,
from one source alternative and with the small exceptional scale excluded. -/
theorem selfDual_strip_rounded_case_two_arm_bounds_all_offsets_of_left
    (q : Set.Ici (1 : ℝ)) (n k : ℕ) (hn : 11 ≤ n)
    (hleft : (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real
      (stripSourceSquareEvent n 0 (sourceSquareSideArmEvent (2*n)
        (4*(((n+8)/9:ℕ):ℤ)) (5*(((n+8)/9:ℕ):ℤ)) 0 (9*(((n+8)/9:ℕ):ℤ)) 0))) :
    ∀ x : ℤ,
      (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoFirstArm n ((n+8)/9) x) ∧
      (1/(36*(k:ℝ)))/6 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoSecondArm n ((n+8)/9) x) := by
  exact selfDual_strip_case_two_arm_bounds_all_offsets_of_left q n ((n+8)/9)
    (rounded_source_translated_rectangles_fit n hn) (1/(36*(k:ℝ))) hleft

end PottsContinuity.Push
