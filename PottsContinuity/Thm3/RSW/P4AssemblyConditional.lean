module

public import PottsContinuity.Thm3.RSW.Prop3Conditional

/-!
# P4 to P5 at the explicit self-dual value, with all links as hypotheses

The corrected decay upgrade of Proposition 4, the annulus recurrence, the reflected
construction and the annulus-to-buffered-RSW implication are hypotheses here. The
reflected construction is derived from the four-corridor circuit statement in
`Thm3.RSW.Prop3Corridor` (via
`maxSquarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit`), and the last
implication from the annulus chain in `Thm3.RSW.P4GeometryConditional` (via
`annulus8_to_buffered_crossings_of_annulusChain`).
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology

/-- P4 rules out the corrected decay alternative and forces a uniform annulus
bound, once the two geometric inputs and the corrected decay upgrade hold. -/
theorem selfDual_P4_uniform_annulus_of_induction1_reflectedFKG_decayUpgrade
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (hp : 0 < p)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hreflectedFKG : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → n ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 n)
    (hdecayUpgrade :
      (∃ c₀ β : ℝ, 0 < c₀ ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c₀*(n:ℝ)^β)) →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)))
    (hrate : Tendsto (fun n : ℕ => 1/(n:ℝ)*Real.log (oneArmProbability μ n)) atTop (𝓝 0)) :
    ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
      a ≤ annulusProbability (selfDualParameters q) 8 n := by
  rcases selfDual_dualityP_corrected_of_induction1_reflectedFKG
      q μ hμ C hC p hp hinduction1 hreflectedFKG with hfirst | hsecond
  · exact hfirst
  · obtain ⟨c, hc, hbound⟩ := hdecayUpgrade hsecond
    exact (oneArm_not_exponential_of_log_rate_zero (selfDualParameters q) μ hμ hrate
      ⟨c, hc, eventually_atTop.mpr ⟨1, hbound⟩⟩).elim

/-- The exact buffered P5 conclusion follows from the preceding chain and the
P5b(R=8) ⇒ P5 implication. Every link is an explicit hypothesis. -/
theorem selfDual_P4_implies_P5_of_induction1_reflectedFKG_decayUpgrade_annulusRSW
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C) (p : ℕ) (hp : 0 < p)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hreflectedFKG : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → n ≤ 7*m →
      (maxSquarePairProbability (selfDualParameters q) m)^p ≤
        annulusProbability (selfDualParameters q) 8 n)
    (hdecayUpgrade :
      (∃ c₀ β : ℝ, 0 < c₀ ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c₀*(n:ℝ)^β)) →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)))
    (hannulusRSW :
      (∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n →
        a ≤ annulusProbability (selfDualParameters q) 8 n) →
      ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        c ≤ bufferedCrossingProbability (selfDualParameters q).toP (selfDualParameters q).toQ α n)
    (hrate : Tendsto (fun n : ℕ => 1/(n:ℝ)*Real.log (oneArmProbability μ n)) atTop (𝓝 0)) :
    ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ bufferedCrossingProbability (selfDualParameters q).toP (selfDualParameters q).toQ α n := by
  apply hannulusRSW
  exact selfDual_P4_uniform_annulus_of_induction1_reflectedFKG_decayUpgrade
    q μ hμ C hC p hp hinduction1 hreflectedFKG hdecayUpgrade hrate

end PottsContinuity.RSW
