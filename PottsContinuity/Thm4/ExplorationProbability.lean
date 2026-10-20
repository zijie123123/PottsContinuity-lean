/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/ParafermionicCoverExplorationProbability.lean`.
Adaptation: exact self-dual PD finite law, closed real [1,4] including endpoint.
-/
module

public import PottsContinuity.Thm4.ExplorationPath
public import PottsContinuity.Thm4.SelfDualParameters
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial MeasureTheory
noncomputable section

local instance coverExplorationProbabilityConfigMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance coverExplorationProbabilityConfigMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- A fixed layered port is visited when it occurs in the support of the actual
unique corner-cut exploration for that configuration. -/
def parafermionicCoverOriginExplorationVisitEvent (n : ℕ) (hn : 1 ≤ n)
    (z : ParafermionicCoverFinitePort n × Bool) :
    Set (Configuration (ParafermionicAmbientGraph n)) :=
  {A | z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support}

theorem parafermionicCoverFiniteOriginCornerPortPrimalVertex_eq_boxOrigin
    (n : ℕ) (hn : 1 ≤ n) :
    parafermionicCoverFinitePortPrimalVertex n
      (parafermionicCoverFiniteOriginCornerPort n hn) =
      parafermionicCoverBoxOrigin n := by
  apply Subtype.ext
  change parafermionicCoverPortVertex
      (parafermionicCoverFiniteOriginCornerPort n hn).1 =
    (parafermionicCoverBoxOrigin n).1
  rw [parafermionicCoverFiniteOriginCornerPort_val,
    parafermionicCoverOriginCornerPort_primalVertex]
  rfl

theorem parafermionicCoverOriginExplorationVisitEvent_subset_actualConnection
    (n : ℕ) (hn : 1 ≤ n) (z : ParafermionicCoverFinitePort n × Bool) :
    parafermionicCoverOriginExplorationVisitEvent n hn z ⊆
      {A | ActualConnected (ParafermionicAmbientGraph n) A
        (parafermionicCoverBoxOrigin n)
        (parafermionicCoverFinitePortPrimalVertex n z.1)} := by
  intro A hA
  have hconn := parafermionicCoverFiniteOriginExplorationPath_support_actualConnected
    n hn A hA
  simpa [parafermionicCoverFiniteOriginCornerPortPrimalVertex_eq_boxOrigin] using hconn

/-- Under the genuine finite free FK law, visiting any fixed layered port in the
chosen exploration costs at most the actual connection probability to its
primal vertex. The visit event is defined without reference to q. -/
theorem parafermionicCoverOriginExplorationVisit_probability_le_connection
    (n : ℕ) (hn : 1 ≤ n) (q : Set.Icc (1 : ℝ) 4)
    (z : ParafermionicCoverFinitePort n × Bool) :
    (((law (ParafermionicAmbientGraph n) (selfDualParameters ⟨q, q.2.1⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      (parafermionicCoverOriginExplorationVisitEvent n hn z)).toReal) ≤
    (((law (ParafermionicAmbientGraph n) (selfDualParameters ⟨q, q.2.1⟩)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      {A | ActualConnected (ParafermionicAmbientGraph n) A
        (parafermionicCoverBoxOrigin n)
        (parafermionicCoverFinitePortPrimalVertex n z.1)}).toReal) := by
  let μ := (law (ParafermionicAmbientGraph n) (selfDualParameters ⟨q, q.2.1⟩)
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
  have hmeasure := MeasureTheory.measure_mono
    (μ := μ) (parafermionicCoverOriginExplorationVisitEvent_subset_actualConnection n hn z)
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
  simpa [μ] using hreal

end
end PottsContinuity.Thm4
