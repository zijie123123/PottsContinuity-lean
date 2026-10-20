module

public import PottsContinuity.Thm3.Push.StripCaseTwoWideArmTranslation
public import PottsContinuity.Thm3.Push.RoundedSourceArmGeometry

@[expose] public section

namespace PottsContinuity.Push

/-- At the explicit self-dual parameter the original first Case 2 arm
supplies the printed second-arm lower bound, with all symmetry steps proved. -/
theorem selfDual_strip_case_two_second_arm_ge_sixth_of_first
    (q : Set.Ici (1 : ℝ)) (n s : ℕ) (x : ℤ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (hfirst : c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoFirstArm n s x)) :
    c₁/6 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseTwoSecondArm n s x) :=
  strip_case_two_second_arm_ge_sixth_of_first (RSW.selfDualParameters q) n s _
    (RSW.selfDualStripMeasure_isLimit q n) x hscale c₁ hfirst

end PottsContinuity.Push
