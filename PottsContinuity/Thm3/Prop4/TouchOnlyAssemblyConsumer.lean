module

public import PottsContinuity.Thm3.Prop4.TouchOnlyPairDichotomy

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- The P4 ⇒ P5 geometry inputs, built by `RSW.p4toP5RemainingGeometryProvider_final` from two
consequences of the touch bound in the proof of Proposition 4 (`dualityQ_corrected_of_touch`
and `evenSquarePairKernel_package_of_touch`). Every selector, band, recurrence and pair-field input
is proved; only the exact touching family of Lemma 6 (`hTouch`) is a hypothesis. -/
noncomputable def p4toP5RemainingGeometryProvider_of_touch
    (hTouch : ∀ q : Set.Ici (1 : ℝ), ∀ k l : ℕ, 1 ≤ k → k ≤ l →
      ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
        1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    Assembly.p4toP5RemainingGeometryProvider :=
  RSW.p4toP5RemainingGeometryProvider_final
    PlanarMixed.StripRSWSelectors.roundedLocalConfinedPrefixSelectorExists
    PlanarMixed.Lemma4Connectors.lemma4_band_to_square_bound
    (fun q μ hμ => dualityQ_corrected_of_touch q μ hμ (hTouch q))
    (fun q μ hμ => evenSquarePairKernel_package_of_touch q μ hμ (hTouch q))

end
end PottsContinuity.Thm3.Prop4
