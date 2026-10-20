module

public import PottsContinuity.Thm3.RSW.Lemma4SourceBandFromStrip

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The source coefficient is exactly the three-window comparison cost
divided by the uniform coefficient of eq. (13). Only the record-free band estimate
(proved as `PlanarMixed.Lemma4Connectors.lemma4_band_to_square_bound`) and strip RSW
remain; no canonical native-carrier identification is used. -/
theorem selfDual_lemma4_coefficient_of_stripRSW_and_bandToSquare
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (hbandToSquare : ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        ((1+(q:ℝ)^2)^3/c₃)*(annulusProbability (selfDualParameters q) 8 n)^2 := by
  obtain ⟨c₃,hc₃,hlower⟩ := selfDual_lemma4_source_band_lower_of_stripRSW q hstrip
  refine ⟨c₃,hc₃,?_⟩
  intro n hn
  have hfree : law (lemma4AmbientGraph n) (selfDualParameters q)
      (frozenBoundaryCondition (box (56*n)) 0) =
      law (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq _ _ _ (by
      simp only [frozenBoundaryCondition,BoundaryCondition.free,ite_true])
  have hl : c₃*annulusProbability (selfDualParameters q) 8 (7*n) ≤
      (measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal := by
    simpa only [PD.FK.measure,hfree] using hlower n hn
  have h := hl.trans (hbandToSquare n hn)
  calc
    _ ≤ ((1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2)/c₃ :=
      (le_div_iff₀ hc₃).mpr (by simpa only [mul_comm] using h)
    _ = _ := by ring

/-- The exact uniform Lemma 4 recurrence, conditional only on strip RSW and
the separate record-free band estimate, with the conventional C>=1. -/
theorem selfDual_lemma4_of_stripRSW_and_bandToSquare
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (hbandToSquare : ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2 := by
  obtain ⟨c₃,hc₃,hbound⟩ := selfDual_lemma4_coefficient_of_stripRSW_and_bandToSquare q hstrip hbandToSquare
  refine ⟨max 1 ((1+(q:ℝ)^2)^3/c₃),le_max_left _ _,?_⟩
  intro n hn
  exact (hbound n hn).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))

end
end PottsContinuity.RSW
