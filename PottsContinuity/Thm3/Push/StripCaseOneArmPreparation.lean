module

public import PottsContinuity.Thm3.Push.StripTopArmTranslation
public import PottsContinuity.Thm3.Push.StripSourceTranslation
public import PottsContinuity.Thm3.Push.StripCaseOneRounded
public import PottsContinuity.Thm3.Push.RoundedSourceArmGeometry

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory
noncomputable section

/-- The confined source top arm is dominated by its original square top arm
under every finite strip measure. -/
theorem strip_top_arm_probability_le_interval_arm (n : ℕ) (x l r L R : ℤ)
    (μ : Measure (RSW.StripConfiguration n)) [IsFiniteMeasure μ] :
    μ.real (stripSourceSquareEvent n x (sourceSquareTopArmEvent (2*n) l r L R)) ≤
      μ.real (stripSourceSquareEvent n x (intervalArmEvent (2*n) l r)) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  exact sourceSquareTopArmEvent_subset_intervalArmEvent (2*n) l r L R hω

/-- The printed top-arm alternative supplies both actual Case 1 square-arm
marginals, by original-bond inclusion and proved strip translation. -/
theorem strip_case_one_arm_bounds_of_top (θ : Parameters) (n s : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (x : ℤ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (htop : c₁/3 ≤ μ.real (stripSourceSquareEvent n x
      (sourceSquareTopArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ))))) :
    c₁/3 ≤ μ.real (stripCaseOneFirstArm n s x) ∧
      c₁/3 ≤ μ.real (stripCaseOneSecondArm n s x) := by
  let hprob : IsProbabilityMeasure μ := hμ.1
  constructor
  · exact htop.trans (strip_top_arm_probability_le_interval_arm n x _ _ _ _ μ)
  · have heq := strip_limit_top_arm_eq_translated_second θ n s μ hμ x hscale
    have hsecond := htop
    rw [heq] at hsecond
    exact hsecond.trans (strip_top_arm_probability_le_interval_arm n x _ _ _ _ μ)

/-- One reference top-arm alternative supplies both Case 1 marginals at
all translated gluing placements, for every real q at least one. -/
theorem selfDual_strip_case_one_arm_bounds_all_offsets_of_top
    (q : Set.Ici (1 : ℝ)) (n s : ℕ) (hscale : 11*s ≤ 2*n) (c₁ : ℝ)
    (htop : c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripSourceSquareEvent n 0
      (sourceSquareTopArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ))))) :
    ∀ x : ℤ,
      c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseOneFirstArm n s x) ∧
      c₁/3 ≤ (RSW.selfDualStripMeasure q n).real (stripCaseOneSecondArm n s x) := by
  intro x
  apply strip_case_one_arm_bounds_of_top (RSW.selfDualParameters q) n s _
    (RSW.selfDualStripMeasure_isLimit q n) x hscale c₁
  have heq := strip_limit_sourceSquareEvent_translation (RSW.selfDualParameters q) n _
    (RSW.selfDualStripMeasure_isLimit q n) 0 x
    (sourceSquareTopArmEvent (2*n) (4*(s:ℤ)) (5*(s:ℤ)) 0 (9*(s:ℤ)))
    (sourceSquareTopArmEvent_isUpperSet _ _ _ _ _)
  rw [heq] at htop
  simpa only [zero_add] using htop

/-- Case 1's exact rounded local bound from just its printed top alternative;
all exploration, both arm marginals, and all translations are discharged. -/
theorem selfDual_strip_rounded_case_one_local_lower_all_offsets_of_top
    (q : Set.Ici (1 : ℝ)) (n k : ℕ) (hn : 11 ≤ n) (hk : 1 ≤ k)
    (htop : (1/(36*(k:ℝ)))/3 ≤ (RSW.selfDualStripMeasure q n).real
      (stripSourceSquareEvent n 0 (sourceSquareTopArmEvent (2*n)
        (4*(((n+8)/9:ℕ):ℤ)) (5*(((n+8)/9:ℕ):ℤ)) 0 (9*(((n+8)/9:ℕ):ℤ))))) :
    ∀ x : ℤ, RSW.stripLocalLower q k ≤ (RSW.selfDualStripMeasure q n).real
      (RSW.stripLocalConnection n ((n+8)/9) x) := by
  have harms := selfDual_strip_case_one_arm_bounds_all_offsets_of_top q n ((n+8)/9)
    (rounded_source_translated_rectangles_fit n hn) (1/(36*(k:ℝ))) htop
  intro x
  exact strip_rounded_case_one_stripLocalLower q k n hk (by omega) x (harms x).1 (harms x).2

end
end PottsContinuity.Push
