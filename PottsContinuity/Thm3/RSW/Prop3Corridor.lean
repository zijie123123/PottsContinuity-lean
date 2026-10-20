module

public import PottsContinuity.Thm3.RSW.CorridorAnnulus
public import PottsContinuity.Thm3.RSW.P4AssemblyConditional

/-!
# Conditional results after the corrected reflected chain is discharged

All reflected-chain probability, finite-domain comparison, integer rounding
and FKG estimates are proved. The four-corridor premise is purely a
q-independent actual-path-to-Jordan-circuit statement. Lemma 4 is an explicit
input, as are the decay upgrade of Proposition 4 and the annulus-to-P5 link.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology

/-- Corrected Proposition-3 at-least-one alternative with no unproved
reflected probability premise. Only the source recurrence and the explicit
deterministic circuit-extraction hypothesis remain conditional. -/
theorem selfDual_dualityP_corrected_of_induction1_fourCorridorCircuit
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hfourCorridorCircuit : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → ∀ ω,
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) ω →
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) ω →
      finiteVerticalCrossing (box (8*n)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      finiteVerticalCrossing (box (8*n)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      ω ∈ annulusCircuitEvent (box (8*n)) (0,0) n)
    : (∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n → a ≤ annulusProbability (selfDualParameters q) 8 n) ∨
      (∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)^β)) := by
  exact selfDual_dualityP_corrected_of_induction1_reflectedFKG q μ hμ C hC 112 (by decide)
    hinduction1 (fun n m hn hm hmn hnm =>
      maxSquarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit
        (selfDualParameters q) n m hn hm hmn hnm (hfourCorridorCircuit n m hn hm hmn))

/-- Exact P4⇒P5 assembly after replacing the reflected probability premise
by the deterministic four-corridor circuit hypothesis. -/
theorem selfDual_P4_implies_P5_of_induction1_fourCorridorCircuit_decayUpgrade_annulusRSW
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)
    (hfourCorridorCircuit : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m < n → ∀ ω,
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ)) ω →
      horizontalCrossing (box (8*n)) (-2*(n:ℤ)) (2*(n:ℤ))
        (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1) ω →
      finiteVerticalCrossing (box (8*n)) (-(n:ℤ)-1-(m:ℤ)) (-(n:ℤ)-1)
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      finiteVerticalCrossing (box (8*n)) ((n:ℤ)+1) ((n:ℤ)+1+(m:ℤ))
        (-2*(n:ℤ)) (2*(n:ℤ)) ω →
      ω ∈ annulusCircuitEvent (box (8*n)) (0,0) n)
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
  exact selfDual_P4_implies_P5_of_induction1_reflectedFKG_decayUpgrade_annulusRSW
    q μ hμ C hC 112 (by decide) hinduction1
    (fun n m hn hm hmn hnm =>
      maxSquarePair_pow_oneHundredTwelve_le_annulus_of_fourCorridorCircuit
        (selfDualParameters q) n m hn hm hmn hnm (hfourCorridorCircuit n m hn hm hmn))
    hdecayUpgrade hannulusRSW hrate

end PottsContinuity.RSW
