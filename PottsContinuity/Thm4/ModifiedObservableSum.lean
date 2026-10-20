module

public import PottsContinuity.Thm4.PathObservable
public import PottsContinuity.Thm4.WindingCancellation

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial MeasureTheory
noncomputable section

local instance modifiedSumConfigFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _
local instance modifiedSumMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance modifiedSumMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The actual modified Bochner expectation is the complete finite FK sum,
including its separate winding branch at q=4. -/
theorem modifiedPathExpectation_eq_configuration_sum
    (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    parafermionicCoverModifiedPathExpectation q n hn z =
      ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n)
          (selfDualParameters ⟨q, q.2.1⟩)
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          parafermionicCoverModifiedPathAtom q n hn A z := by
  classical
  rw [parafermionicCoverModifiedPathExpectation, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [law_apply]
  have hp := (configurationProbability_pos (ParafermionicAmbientGraph n)
    (selfDualParameters ⟨q, q.2.1⟩)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A).le
  simp [ENNReal.toReal_ofReal hp, RCLike.real_smul_eq_coe_smul (K := ℂ)]

theorem modifiedPathExpectation_four_eq_winding_sum (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    parafermionicCoverModifiedPathExpectation ⟨4, by norm_num⟩ n hn z =
      ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n)
          (selfDualParameters ⟨4, by norm_num⟩)
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          (parafermionicCoverPathWindingAtom n hn A z : ℂ) := by
  rw [modifiedPathExpectation_eq_configuration_sum]
  simp only [parafermionicCoverModifiedPathAtom, ↓reduceIte]

/-- The expected signed winding contribution of each actual finite edge is zero. -/
theorem modifiedPathExpectation_four_edge_defect_zero (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (∑ c ∈ windingEdgePorts n e,
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
        parafermionicCoverModifiedPathExpectation ⟨4, by norm_num⟩ n hn (c, true)) = 0 := by
  classical
  simp_rw [modifiedPathExpectation_four_eq_winding_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsum : (∑ A : Configuration (ParafermionicAmbientGraph n),
      ∑ c ∈ windingEdgePorts n e,
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
          ((configurationProbability (ParafermionicAmbientGraph n)
            (selfDualParameters ⟨4, by norm_num⟩)
            (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
            (parafermionicCoverPathWindingAtom n hn A (c, true) : ℂ))) =
      ((∑ A : Configuration (ParafermionicAmbientGraph n),
        configurationProbability (ParafermionicAmbientGraph n)
          (selfDualParameters ⟨4, by norm_num⟩)
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A *
            windingAtomicDefect n hn e A : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, windingAtomicDefect]
    apply Finset.sum_congr rfl
    intro A _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> push_cast <;> ring
  rw [hsum, windingAtomicDefect_configuration_sum_four]
  rfl

end
end PottsContinuity.Thm4
