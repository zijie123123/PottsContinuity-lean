module

public import PottsContinuity.Thm3.RSW.FourCorridorCircuit
public import PottsContinuity.Thm3.RSW.Prop3Corridor
public import PottsContinuity.Thm3.RSW.P4GeometryConditional
public import PottsContinuity.Thm3.RSW.P5bConditional
public import PottsContinuity.Thm3.RSW.BufferedAnnulusGluing

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology
noncomputable section

/-- Corrected Proposition-3 alternative conditional only on the actual
Lemma-4 recurrence. The stretched rate includes its positive coefficient. -/
theorem selfDual_dualityP_corrected_of_induction1
    (q : Set.Ici (1:ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit (selfDualParameters q).toP (selfDualParameters q).toQ 0 μ)
    (C : ℝ) (hC : 1 ≤ C)
    (hinduction1 : ∀ n : ℕ, 1 ≤ n →
      annulusProbability (selfDualParameters q) 8 (7*n) ≤
        C*(annulusProbability (selfDualParameters q) 8 n)^2)

    : (∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 1 ≤ n → a ≤ annulusProbability (selfDualParameters q) 8 n) ∨
      (∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ n : ℕ, 1 ≤ n →
        oneArmProbability μ n ≤ Real.exp (-c*(n:ℝ)^β)) := by
  exact selfDual_dualityP_corrected_of_induction1_fourCorridorCircuit
    q μ hμ C hC hinduction1 fourCorridor_annulusCircuitEvent

end
end PottsContinuity.RSW
