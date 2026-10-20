module

public import PottsContinuity.Thm3.RSW.Lemma4BandFactorOfStripRSW

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.RCInfinite MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The uniform source band factor under the actual frozen finite free law,
conditional only on Lemma2, with one coefficient before all positive scales. -/
theorem selfDual_lemma4_band_factor_frozen_of_stripRSW
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (frozenBoundaryCondition (box (56*n)) 0) (lemma4AnnulusPairEvent n)).toReal ≤
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (frozenBoundaryCondition (box (56*n)) 0) (lemma4BandConstructionEvent n)).toReal := by
  obtain ⟨c,hc,hbound⟩ := selfDual_lemma4_band_factor_of_stripRSW q hstrip
  refine ⟨c,hc,?_⟩
  intro n hn
  have hfree : law (lemma4AmbientGraph n) (selfDualParameters q)
      (frozenBoundaryCondition (box (56*n)) 0) =
      law (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq _ _ _ (by
      simp only [frozenBoundaryCondition,BoundaryCondition.free,ite_true])
  simpa only [PD.FK.measure,hfree] using hbound n hn

end
end PottsContinuity.RSW
