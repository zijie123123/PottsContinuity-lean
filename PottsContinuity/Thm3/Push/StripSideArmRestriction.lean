module

public import PottsContinuity.Thm3.Push.SourceSideArmRestriction
public import PottsContinuity.Thm3.Push.StripSourceCylinder

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The source wider-to-narrower restriction holds under every finite strip
measure, without a reflection or boundary-condition hypothesis. -/
theorem strip_source_side_arm_le_sum (n : ℕ) (x l r L₀ R₀ T L R : ℤ)
    (hl : L ≤ l) (hr : r ≤ R) (hT : T ≤ L ∨ R ≤ T)
    (μ : Measure (RSW.StripConfiguration n)) [IsFiniteMeasure μ] :
    μ.real (stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n) l r L₀ R₀ T)) ≤
      μ.real (stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n) l r L R L)) +
        μ.real (stripSourceSquareEvent n x (sourceSquareSideArmEvent (2*n) l r L R R)) := by
  apply le_trans (measureReal_mono (h₂ := measure_ne_top _ _) ?_)
    (measureReal_union_le _ _)
  intro ω hω
  exact sourceSquareSideArmEvent_subset_side_union (2*n) l r L₀ R₀ T L R hl hr hT hω

/-- The actual Case 2 wider arm supplies a half-sized bound on at least one
side of R'. Selecting the left side additionally uses strip symmetry. -/
theorem strip_source_case_two_wide_arm_one_side (n s : ℕ) (c₁ : ℝ)
    (offset : ℤ) (μ : Measure (RSW.StripConfiguration n)) [IsFiniteMeasure μ]
    (hwide : c₁/3 ≤ μ.real (stripSourceSquareEvent n offset
      (sourceSquareSideArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ))
        (2*(s:ℤ)) (11*(s:ℤ)) (11*(s:ℤ))))) :
    c₁/6 ≤ μ.real (stripSourceSquareEvent n offset (sourceCaseTwoSecondArm n s)) ∨
      c₁/6 ≤ μ.real (stripSourceSquareEvent n offset
        (sourceSquareSideArmEvent (2*n) (6*(s:ℤ)) (7*(s:ℤ))
          (4*(s:ℤ)) (9*(s:ℤ)) (9*(s:ℤ)))) := by
  have hsum := strip_source_side_arm_le_sum n offset (6*(s:ℤ)) (7*(s:ℤ))
    (2*(s:ℤ)) (11*(s:ℤ)) (11*(s:ℤ)) (4*(s:ℤ)) (9*(s:ℤ))
    (by omega) (by omega) (Or.inr (by omega)) μ
  by_contra h
  push Not at h
  change _ < _ ∧ _ < _ at h
  dsimp only [sourceCaseTwoSecondArm] at h
  linarith only [hwide,hsum,h.1,h.2]

end
end PottsContinuity.Push
