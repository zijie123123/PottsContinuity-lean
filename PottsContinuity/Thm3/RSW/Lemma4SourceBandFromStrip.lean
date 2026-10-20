module

public import PottsContinuity.Thm3.OuterCircuit.RootRecords
public import PottsContinuity.Thm3.RSW.Lemma4BandFactorFrozen

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Source eq. (13) from strip RSW, with the actual outermost open-circuit
records supplied by the built provider. The coefficient is uniform in scale. -/
theorem selfDual_lemma4_source_band_lower_of_stripRSW (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * annulusProbability (selfDualParameters q) 8 (7*n) ≤
        (measure (lemma4AmbientGraph n) (selfDualParameters q)
          (frozenBoundaryCondition (box (56*n)) 0) (lemma4BandConstructionEvent n)).toReal := by
  obtain ⟨ca,hca,hannuli⟩ := OuterCircuit.selfDual_lemma4_two_annuli_lower q
  obtain ⟨cb,hcb,hbands⟩ := selfDual_lemma4_band_factor_frozen_of_stripRSW q hstrip
  refine ⟨cb*ca,mul_pos hcb hca,?_⟩
  intro n hn
  have hmul := mul_le_mul_of_nonneg_left (hannuli n hn) hcb.le
  rw [← mul_assoc] at hmul
  exact hmul.trans (hbands n hn)

end
end PottsContinuity.RSW
