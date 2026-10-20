module

public import PottsContinuity.Thm3.RSW.Prop3Corridor
public import PottsContinuity.Thm3.RSW.P5bConditional

/-!
# P4 to P5 after both probabilistic gluing chains are proved

The recurrence of Lemma 4, two deterministic geometry statements and the corrected
decay upgrade of Proposition 4 are hypotheses here. No entire RSW implication or
reflected-pair probability inequality is taken as an input. The theorem is used by
`Assembly.p4_implies_p5_of_geometryInputs`; for the self-dual law its inputs are
supplied in `Assembly.p4toP5GeometryProvider_of_remainingInputs`, the geometry by
`RSW.fourCorridor_annulusCircuitEvent` and `RSW.buffered_annulus_chain_glues`.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology

/-- Exact buffered P5 from P4, with the source recurrence, the deterministic
four-corridor/circuit-chain geometry and the corrected decay upgrade as hypotheses. -/
theorem selfDual_P4_implies_P5_of_induction1_fourCorridorCircuit_decayUpgrade_annulusChain
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
    (hannulusChain : ∀ α : ℝ, 0 < α → ∀ n m K : ℕ, 32 ≤ n → 1 ≤ m →
      ∀ (hscale : 16*m ≤ n) (hspan : (K*m:ℕ) ≤ ⌊α*(n:ℝ)⌋+(m:ℤ)),
      ⌊α*(n:ℝ)⌋ ≤ (K*m:ℕ) → ∀ ω,
      (∀ l : Fin (K+1), ω ∈ bufferedAnnulusChainLocalEvent α n m K hscale hspan l) →
      horizontalCrossing
        (latticeRectangle (-(n:ℤ)) ⌊(α+1)*(n:ℝ)⌋ (-(n:ℤ)) (2*(n:ℤ)))
        0 ⌊α*(n:ℝ)⌋ 0 n ω)
    (hrate : Tendsto (fun n : ℕ => 1/(n:ℝ)*Real.log (oneArmProbability μ n)) atTop (𝓝 0)) :
    ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ bufferedCrossingProbability (selfDualParameters q).toP (selfDualParameters q).toQ α n := by
  exact selfDual_P4_implies_P5_of_induction1_fourCorridorCircuit_decayUpgrade_annulusRSW
    q μ hμ C hC hinduction1 hfourCorridorCircuit hdecayUpgrade
    (fun huniform => annulus8_to_buffered_crossings_of_annulusChain
      (selfDualParameters q) huniform hannulusChain) hrate

end PottsContinuity.RSW
