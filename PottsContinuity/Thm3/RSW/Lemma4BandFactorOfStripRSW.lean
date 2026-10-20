module

public import PottsContinuity.Thm3.RSW.Lemma4CoreComparison
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualBandInclusion
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualComparisonConditional

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality MeasureTheory
noncomputable section

/-- The source band factor at every scale, conditional only on Lemma2.
All finite dual laws, native path transfers and domain comparisons are proved. -/
theorem selfDual_lemma4_band_factor_of_stripRSW
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (PD.FK.measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4AnnulusPairEvent n)).toReal ≤
      (PD.FK.measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal :=
  selfDual_lemma4_band_factor_of_nativeBandInclusion_and_coreComparison_and_stripRSW
    q hstrip lemma4_nativeDualBand_subset_sourceDualBand (lemma4_symmetric_reference_le_nativeDualBand q)

end
end PottsContinuity.RSW
