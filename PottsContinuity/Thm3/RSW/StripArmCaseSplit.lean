module

public import PottsContinuity.Thm3.RSW.StripReflectionArm
public import PottsContinuity.Thm3.RSW.StripThreeSideExit

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- Reflection invariance of the actual strip law gives the source's top/left
case split. The seed event is confined to the correct height band. -/
theorem strip_arm_case_split_of_reflectionInvariant (n : ℕ) (l r H a b : ℤ)
    (hla : l ≤ a) (hbr : b ≤ r) (hcenter : a+b = l+r)
    (μ : Measure (StripConfiguration n)) [IsFiniteMeasure μ]
    (hμ : μ.map (stripHorizontalReflectionConfiguration n (l+r)) = μ)
    (c : ℝ) (hc : c ≤ μ.real (stripBandArm n H a b)) :
    c/3 ≤ μ.real (stripRectangleArm n l r H a b {v | v.val.2 = H}) ∨
    c/3 ≤ μ.real (stripRectangleArm n l r H a b {v | v.val.1 = l}) := by
  let T := stripRectangleArm n l r H a b {v | v.val.2 = H}
  let L := stripRectangleArm n l r H a b {v | v.val.1 = l}
  let R := stripRectangleArm n l r H a b {v | v.val.1 = r}
  have hpre : (stripHorizontalReflectionConfiguration n (l+r)) ⁻¹' L = R := by
    ext ω
    exact stripRectangleArm_left_reflection_iff n l r H a b hcenter ω
  have hL : MeasurableSet L := (stripConfinedConnection_isClopen n _ _ _).isOpen.measurableSet
  have hLR : μ.real L = μ.real R := by
    calc
      μ.real L = (μ.map (stripHorizontalReflectionConfiguration n (l+r))).real L := by rw [hμ]
      _ = μ.real ((stripHorizontalReflectionConfiguration n (l+r)) ⁻¹' L) := by
        unfold Measure.real
        rw [Measure.map_apply (stripHorizontalReflectionConfiguration n (l+r)).continuous.measurable
          hL]
      _ = μ.real R := by rw [hpre]
  have hcover : μ.real (stripBandArm n H a b) ≤ μ.real (T ∪ (L ∪ R)) :=
    measureReal_mono (stripBandArm_subset_three_rectangleArms n l r H a b hla hbr)
  have houter := measureReal_union_le (μ := μ) T (L ∪ R)
  have hinner := measureReal_union_le (μ := μ) L R
  by_contra h
  push Not at h
  change μ.real T < c/3 ∧ μ.real L < c/3 at h
  linarith only [hc,hcover,houter,hinner,hLR,h.1,h.2]

end PottsContinuity.RSW
