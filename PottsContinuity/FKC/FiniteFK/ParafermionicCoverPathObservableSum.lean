-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverPathObservableSum.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverPathObservable
public import PottsContinuity.FKC.FiniteFK.CriticalEdgeToggle
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
open scoped BigOperators
noncomputable section

local instance pathObservableSumConfigFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _
local instance pathObservableSumConfigMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance pathObservableSumConfigMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

theorem parafermionicCoverPathPhaseExpectation_eq_configuration_sum
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    parafermionicCoverPathPhaseExpectation q n hn z =
      ∑ A : Configuration (ParafermionicAmbientGraph n),
        (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
          parafermionicCoverPathPhaseAtom q n hn A z := by
  classical
  rw [parafermionicCoverPathPhaseExpectation, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [law_apply]
  have hp := (configurationProbability_pos (ParafermionicAmbientGraph n) q
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A).le
  simp [ENNReal.toReal_ofReal hp, RCLike.real_smul_eq_coe_smul (K := ℂ)]

end
end PottsContinuity.FKC.FiniteFK
