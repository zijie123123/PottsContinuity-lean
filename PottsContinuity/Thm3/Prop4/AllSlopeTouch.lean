module

public import PottsContinuity.Thm3.Prop4.DenominatorTouch
public import PottsContinuity.Thm3.Prop4.SlopeProbability
public import PottsContinuity.Thm3.Prop4.TiltedSelfDual

/-!
# All-slope conditional touch estimate at the explicit self-dual value

The arbitrary-slope reduction is fully proved. The only probability premises
are the named mixed-duality half bound and the actual explored-strip comparison,
needed only on rational representatives with denominator≤2m. They are explicit
hypotheses here, not Lemma 6 itself. The absolute corrected coefficient is 20;
the earlier integral-m helper retains its sharper coefficient 12.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Corrected touch bound for every real slope in [-1,1], with the two remaining
probabilistic interfaces required only at bounded-denominator rational slopes.
No integrality condition remains on the slope in the conclusion. -/
theorem selfDual_tilted_touch_all_slopes_corrected_of_dualityHalf_and_stripComparison
    (q : Set.Ici (1 : ℝ)) (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hhalf : ∀ (d : ℕ) (a : ℤ), 1 ≤ d → d ≤ 2*m →
      (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 →
      (1/2 : ℝ) ≤ (selfDualTiltedStripMeasure q (2*n) ((a : ℝ)/(d : ℝ))).real
        {ω | lowestTopConnectedHeight (2*n) (by omega) ((a : ℝ)/(d : ℝ)) ω 0 ≤ n})
    (hcomparison : ∀ (d : ℕ) (a : ℤ), 1 ≤ d → d ≤ 2*m →
      (a : ℝ)/(d : ℝ) ∈ Set.Icc (-1 : ℝ) 1 →
      ∀ z ∈ tiltedCandidates n (n*d*m) ((a : ℝ)/(d : ℝ)),
        (selfDualTiltedStripMeasure q (2*n) ((a : ℝ)/(d : ℝ))).real
          (tiltedIsolationAt (2*n) n m ((a : ℝ)/(d : ℝ)) z) ≤
            tiltedTouchProbability (RSW.selfDualParameters q) n m ((a : ℝ)/(d : ℝ))) :
    ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(n : ℝ)^2*(m : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) n m t := by
  intro t ht
  obtain ⟨d,a,hd,hdm,hs,hprob⟩ := tiltedTouchProbability_bounded_denominator_representative
    (RSW.selfDualParameters q) n m (hn.trans hnm) t ht
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hprob]
  exact tilted_touch_denominator_corrected_of_dualityHalf_and_stripComparison
    (RSW.selfDualParameters q) n m d hn (hn.trans hnm) hd hdm _ hs
    ⟨a,div_mul_cancel₀ _ hdR.ne'⟩ _
    (hhalf d a hd hdm hs) (hcomparison d a hd hdm hs)

end PottsContinuity.Thm3.Prop4
