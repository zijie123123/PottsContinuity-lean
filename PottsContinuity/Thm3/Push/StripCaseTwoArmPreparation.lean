module

public import PottsContinuity.Thm3.Push.StripCaseTwoFirstArmSymmetry
public import PottsContinuity.Thm3.Push.StripCaseTwoRoundedArmBound

@[expose] public section

namespace PottsContinuity.Push

/-- The printed left-arm alternative of source Case 2 supplies BOTH original
limiting marginal bounds, with translation and both reflections discharged. -/
theorem selfDual_strip_case_two_arm_bounds_of_left (q : Set.Ici (1 : ℝ)) (n s : ℕ)
    (x : ℤ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (hleft : c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripSourceSquareEvent n x
      (sourceSquareSideArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)) 0))) :
    c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x) ∧
      c₁/6 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoSecondArm n s x) := by
  have heq := strip_limit_case_two_left_eq_first (RSW.selfDualParameters q) n s _
    (RSW.selfDualStripMeasure_isLimit q n) x (by omega)
  have hf : c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x) := by
    change c₁/3 ≤ (RSW.selfDualStripMeasure q n).real
      (stripSourceSquareEvent n x (sourceCaseTwoFirstArm n s))
    rw [← heq]
    exact hleft
  exact ⟨hf,selfDual_strip_case_two_second_arm_ge_sixth_of_first q n s x hscale c₁ hf⟩

end PottsContinuity.Push
