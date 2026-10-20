module

public import PottsContinuity.Thm3.RSW.Lemma4SideReferencePushConditional

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The source band construction has a uniform positive factor relative to
the actual annulus pair once the explicit finite dual-push comparison and
Lemma2 strip bound are supplied. No source-conditioning premise is hidden. -/
theorem selfDual_lemma4_band_factor_of_dualPushComparison_and_stripRSW
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (hdualPushComparison : ∀ n : ℕ, 2 ≤ n → ∀ i : Fin 2,
      selfDualTopWiredCrossingProbability q 180 180 (n/2) ≤
        lemma4SideReferenceProbability (selfDualParameters q) n i) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4AnnulusPairEvent n)).toReal ≤
      (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal := by
  obtain ⟨c,hc,hbound⟩ :=
    selfDual_lemma4SideReference_lower_of_dualPushComparison_and_stripRSW q hstrip hdualPushComparison
  refine ⟨c^2,pow_pos hc _,?_⟩
  intro n hn
  have hprod : c^2 ≤ lemma4SideReferenceProbability (selfDualParameters q) n 0 *
      lemma4SideReferenceProbability (selfDualParameters q) n 1 := by
    simpa only [pow_two] using mul_le_mul (hbound n hn 0) (hbound n hn 1) hc.le
      (lemma4SideReferenceProbability_nonneg _ n 0)
  exact (mul_le_mul_of_nonneg_right hprod ENNReal.toReal_nonneg).trans
    (lemma4_band_reference_product_lower (selfDualParameters q) n)

end
end PottsContinuity.RSW
