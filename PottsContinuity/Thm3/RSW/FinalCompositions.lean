module

public import PottsContinuity.Thm3.RSW.LocalPrefixBandConsequences
public import PottsContinuity.Assembly.FourCorridorAssembly

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section

/-- Lemma 2 (strip RSW) at all scales, from the physical prefix-selector family
`hchoices`. The strip reflection symmetry is proved, not assumed. -/
theorem selfDual_stripRSW_final
    (hchoices : ∀ n : ℕ, ∀ hn : 13 ≤ n,
      Push.RoundedLocalConfinedPrefixSelectorExists n hn) :
    ∀ (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4) (K : ℝ),
      1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
        c ≤ selfDualStripHorizontalProbability ⟨q,hq.1⟩ K s := by
  intro q hq
  exact Push.selfDual_stripRSW_of_localConfinedPrefixSelectors ⟨q,hq.1⟩ hchoices

/-- Lemma 4 in the exact induction form, using the proved two-annuli lower
bound through the source-band lower bound. -/
theorem lemma4_recurrence_final
    (q : Set.Ici (1 : ℝ))
    (hbandToSquare : ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hstrip : ∀ K : ℝ, 1 ≤ K → ∃ c : ℝ, 0 < c ∧ ∀ s : ℕ, 1 ≤ s →
      c ≤ selfDualStripHorizontalProbability q K s) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2 :=
  selfDual_lemma4_of_stripRSW_and_bandToSquare q hstrip hbandToSquare

/-- The P4 ⇒ P5 geometry inputs `Assembly.p4toP5RemainingGeometryProvider` from their
remaining hypotheses. Its pair-kernel field is supplied explicitly by `hpair`: the separate
decay implication `_hdualityQ` does not construct that field and is not used here. -/
noncomputable def p4toP5RemainingGeometryProvider_final
    (hchoices : ∀ n : ℕ, ∀ hn : 13 ≤ n,
      Push.RoundedLocalConfinedPrefixSelectorExists n hn)
    (hbandToSquare : ∀ q : Set.Ici (1 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (measure (lemma4AmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal ≤
      (1+(q:ℝ)^2)^3*(annulusProbability (selfDualParameters q) 8 n)^2)
    (_hdualityQ : ∀ (q : Set.Ici (1 : ℝ))
      (μ : MeasureTheory.Measure (squareLattice.edgeSet → Bool)),
      IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
        (RSW.selfDualParameters q).toQ 0 μ →
      (∃ c₀ α : ℝ, 0 < c₀ ∧ 0 < α ∧ ∀ n : ℕ, 1 ≤ n →
        RSW.oneArmProbability μ n ≤ Real.exp (-c₀ * (n : ℝ)^α)) →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        RSW.oneArmProbability μ n ≤ Real.exp (-c * (n : ℝ)))
    (hpair : ∀ (q : Set.Ici (1 : ℝ))
      (μ : Measure (squareLattice.edgeSet → Bool)),
      IsRCInfiniteVolumeLimit (selfDualParameters q).toP
        (selfDualParameters q).toQ 0 μ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
          maxSquarePairProbability (selfDualParameters q) (2*m) ≤
            A * PottsContinuity.Thm3.Prop4.prop4PairKernel c ε
              (oneArmProbability μ) m) :
    Assembly.p4toP5RemainingGeometryProvider := by
  intro q p μ hp hμ
  have hpθ : p = (selfDualParameters q).toP := by
    apply Subtype.ext
    exact hp
  have hμθ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP
      (selfDualParameters q).toQ 0 μ := by
    rw [hpθ] at hμ
    exact hμ
  let recurrence := lemma4_recurrence_final q (hbandToSquare q)
    (Push.selfDual_stripRSW_of_localConfinedPrefixSelectors q hchoices)
  let pairs := hpair q μ hμθ
  exact {
    C := Classical.choose recurrence
    hC := (Classical.choose_spec recurrence).1
    hinduction1 := (Classical.choose_spec recurrence).2
    ε₀ := Classical.choose pairs
    hε₀ := (Classical.choose_spec pairs).1
    hpair := (Classical.choose_spec pairs).2
  }

end
end PottsContinuity.RSW
