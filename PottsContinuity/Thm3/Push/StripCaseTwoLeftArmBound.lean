module

public import PottsContinuity.Thm3.Push.StripCaseTwoSideSymmetry
public import PottsContinuity.Thm3.Push.StripSideArmRestriction

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The actual source Case 2 wider J arm yields the specified LEFT arm
with the printed factor one sixth, using proved strip symmetries. -/
theorem strip_case_two_left_arm_ge_sixth (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 9*s ≤ 2*n) (c₁ : ℝ)
    (hwide : c₁/3 ≤ μ.real (stripSourceSquareEvent n x
      (sourceSquareSideArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ))
        (2*(s:ℤ)) (11*(s:ℤ)) (11*(s:ℤ))))) :
    c₁/6 ≤ μ.real (stripSourceSquareEvent n x (sourceCaseTwoSecondArm n s)) := by
  let hprob : IsProbabilityMeasure μ := hμ.1
  have hsides := strip_limit_case_two_source_sides_eq θ n s μ hμ x hscale
  rcases strip_source_case_two_wide_arm_one_side n s c₁ x μ hwide with h | h
  · exact h
  · rwa [← hsides] at h

end
end PottsContinuity.Push
