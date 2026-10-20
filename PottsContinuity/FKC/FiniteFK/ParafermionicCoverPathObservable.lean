-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverPathObservable.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhase
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExplorationProbability
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section

local instance pathObservableConfigMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance pathObservableConfigMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The Bochner expectation of the actual finite exploration-path phase atom
under the genuine free FK law on the finite cover box. -/
def parafermionicCoverPathPhaseExpectation (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (z : ParafermionicCoverFinitePort n × Bool) : ℂ :=
  ∫ A, parafermionicCoverPathPhaseAtom q n hn A z ∂
    (law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure

theorem parafermionicCoverPathPhaseExpectation_norm_le_visit
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    ‖parafermionicCoverPathPhaseExpectation q n hn z‖ ≤
      (((law (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
        (parafermionicCoverOriginExplorationVisitEvent n hn z)).toReal) := by
  let μ := (law (ParafermionicAmbientGraph n) q
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := μ) (fun A => parafermionicCoverPathPhaseAtom q n hn A z)
  have hnormfun : (fun A => ‖parafermionicCoverPathPhaseAtom q n hn A z‖) =
      (parafermionicCoverOriginExplorationVisitEvent n hn z).indicator
        (fun _ => (1 : ℝ)) := by
    funext A
    by_cases hz : z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
    · simp [hz, parafermionicCoverOriginExplorationVisitEvent,
        parafermionicCoverPathPhaseAtom_norm, Set.indicator]
    · simp [hz, parafermionicCoverOriginExplorationVisitEvent,
        parafermionicCoverPathPhaseAtom_norm, Set.indicator]
  rw [show parafermionicCoverPathPhaseExpectation q n hn z =
      ∫ A, parafermionicCoverPathPhaseAtom q n hn A z ∂μ by rfl]
  have hind := MeasureTheory.integral_indicator_one
    (μ := μ)
    (s := parafermionicCoverOriginExplorationVisitEvent n hn z)
    (by simp : MeasurableSet (parafermionicCoverOriginExplorationVisitEvent n hn z))
  rw [hnormfun] at hnorm
  simpa [μ, MeasureTheory.measureReal_def] using hnorm.trans_eq hind

theorem parafermionicCoverPathPhaseExpectation_norm_le_connection
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    ‖parafermionicCoverPathPhaseExpectation q n hn z‖ ≤
      (((law (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
        {A | ActualConnected (ParafermionicAmbientGraph n) A
          (parafermionicCoverBoxOrigin n)
          (parafermionicCoverFinitePortPrimalVertex n z.1)}).toReal) := by
  exact (parafermionicCoverPathPhaseExpectation_norm_le_visit q n hn z).trans
    (parafermionicCoverOriginExplorationVisit_probability_le_connection n hn q z)

theorem parafermionicCoverPathPhaseExpectation_target
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    parafermionicCoverPathPhaseExpectation q n hn
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) = 1 := by
  let μ := (law (ParafermionicAmbientGraph n) q
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
  have hpoint : (fun A => parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true)) = fun _ => (1 : ℂ) := by
    funext A
    exact parafermionicCoverPathPhaseAtom_target q n hn A
  rw [show parafermionicCoverPathPhaseExpectation q n hn
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) =
      ∫ A, parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn), true) ∂μ by rfl]
  rw [hpoint, MeasureTheory.integral_const]
  simp [μ, MeasureTheory.measureReal_def]

end
end PottsContinuity.FKC.FiniteFK
