module

public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import PottsContinuity.Thm3.RSW.Lemma4SideDualBandProbability
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualBand
public import PottsContinuity.Thm3.RSW.Lemma4PaddedPushComparison
public import PottsContinuity.Thm3.RSW.Lemma4UniformBandsConditional

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The two remaining native graph/event interfaces imply the earlier padded
comparison. All law transfer, enclosing comparison and measure monotonicity
are discharged here; neither native interface is asserted as proved. -/
theorem lemma4_side_reference_ge_padded_push_of_nativeBandInclusion_and_coreComparison
    (q : Set.Ici (1:ℝ))
    (hNativeBandInclusion : ∀ n : ℕ, ∀ i : Fin 2,
      lemma4NativeDualBandEvent n ⊆ lemma4SideInducedDualBandEvent n i)
    (hCoreComparison : ∀ n : ℕ, 2 ≤ n →
      selfDualTopWiredCrossingProbability q
        ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) ≤
      (PD.FK.measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n))
        (selfDualParameters q)
        (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
        (lemma4NativeDualBandEvent n)).toReal)
    (n : ℕ) (hn : 2 ≤ n) (i : Fin 2) :
    selfDualTopWiredCrossingProbability q 180 180 (n/2) ≤
      lemma4SideReferenceProbability (selfDualParameters q) n i := by
  rw [lemma4SideReferenceProbability_eq_inducedDual]
  exact (lemma4_padded_push_le_symmetric_reference q n hn).trans
    ((hCoreComparison n hn).trans
      (measureReal_mono (h₂ := measure_ne_top _ _) (hNativeBandInclusion n i)))

/-- The source B-n factor follows from Lemma2 and precisely the two remaining
native graph/event interfaces. The real constant is chosen before every
scale; scale one uses the previously proved original positive sample. -/
theorem selfDual_lemma4_band_factor_of_nativeBandInclusion_and_coreComparison_and_stripRSW
    (q : Set.Ici (1:ℝ))
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s)
    (hNativeBandInclusion : ∀ n : ℕ, ∀ i : Fin 2,
      lemma4NativeDualBandEvent n ⊆ lemma4SideInducedDualBandEvent n i)
    (hCoreComparison : ∀ n : ℕ, 2 ≤ n →
      selfDualTopWiredCrossingProbability q
        ((56*(n:ℝ)+1)/(n-1:ℕ)) ((54*(n:ℝ))/(n-1:ℕ)) (n-1) ≤
      (PD.FK.measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n))
        (selfDualParameters q)
        (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
        (lemma4NativeDualBandEvent n)).toReal) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (PD.FK.measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4AnnulusPairEvent n)).toReal ≤
      (PD.FK.measure (lemma4AmbientGraph n) (selfDualParameters q) (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal :=
  selfDual_lemma4_band_factor_of_dualPushComparison_and_stripRSW q hstrip
    (lemma4_side_reference_ge_padded_push_of_nativeBandInclusion_and_coreComparison q
      hNativeBandInclusion hCoreComparison)

end
end PottsContinuity.RSW
