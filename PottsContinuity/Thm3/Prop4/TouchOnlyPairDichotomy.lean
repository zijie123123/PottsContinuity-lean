module

public import PottsContinuity.Thm3.Prop4.PolynomialPairPackage
public import PottsContinuity.Thm3.Prop4.AnnulusArmPolynomialLower
public import PottsContinuity.Thm3.Prop4.TouchOnlyPairPackage
public import PottsContinuity.Thm3.Prop4.RawSourceDecay
public import PottsContinuity.Thm3.RSW.Prop3Geometry
public import PottsContinuity.Thm3.RSW.FinalCompositions
public import PottsContinuity.PlanarMixed.StripRSWSelectors.RoundedLocalSelector
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceEq15

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The exact requested pair-field package has no decay hypothesis. The
proved Proposition3 alternative supplies either the stretched branch or an
actual polynomial arm lower bound, so only touching remains external. -/
theorem evenSquarePairKernel_package_of_touch
    (q : Set.Ici (1 : ℝ)) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
        RSW.maxSquarePairProbability (RSW.selfDualParameters q) (2*m) ≤
          A*prop4PairKernel c ε (RSW.oneArmProbability μ) m := by
  obtain ⟨C,hC,hrec⟩ := RSW.lemma4_recurrence_final q
    (PlanarMixed.Lemma4Connectors.lemma4_band_to_square_bound q)
    (Push.selfDual_stripRSW_of_localConfinedPrefixSelectors q
      PlanarMixed.StripRSWSelectors.roundedLocalConfinedPrefixSelectorExists)
  rcases RSW.selfDual_dualityP_corrected_of_induction1 q μ hμ C hC hrec with hannulus | hstretched
  · obtain ⟨a,ha,hannulus⟩ := hannulus
    apply evenSquarePairKernel_package_of_polynomial_lower q μ hμ (a/25) 2 (div_pos ha (by norm_num))
    intro n hn
    simpa only [Real.rpow_two] using oneArm_polynomial_lower_of_uniform_annulus q μ hμ a ha hannulus n hn
  · exact evenSquarePairKernel_package_of_touch_and_stretchedDecay q μ hμ hTouch hstretched

end
end PottsContinuity.Thm3.Prop4
