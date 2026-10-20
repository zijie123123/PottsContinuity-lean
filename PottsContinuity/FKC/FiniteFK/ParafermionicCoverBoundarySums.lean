-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverBoundarySums.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverContourSum
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSideBoundary
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConnectionProbability
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalSheets
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverExtremalDecayLimit
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section

local instance coverBoundarySumsConfigurationMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance coverBoundarySumsConfigurationMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The actual free finite-FK connection probability from the literal box
origin to a cover vertex, extended by zero outside the finite carrier. -/
def parafermionicCoverBoxOriginConnectionWeight
    (n : ℕ) (q : ClusterWeight) (v : ParafermionicCoverVertex) : ℝ :=
  if hv : v ∈ parafermionicCoverBoxVertices n then
    ((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      {A | ActualConnected (ParafermionicAmbientGraph n) A
        (parafermionicCoverBoxOrigin n) ⟨v, hv⟩}).toReal
  else 0

theorem parafermionicCoverBoxOriginConnectionWeight_nonneg
    (n : ℕ) (q : ClusterWeight) (v : ParafermionicCoverVertex) :
    0 ≤ parafermionicCoverBoxOriginConnectionWeight n q v := by
  unfold parafermionicCoverBoxOriginConnectionWeight
  split_ifs <;> positivity

@[simp] theorem parafermionicCoverBoxOriginConnectionWeight_subtype
    (n : ℕ) (q : ClusterWeight) (v : ParafermionicAmbientVertex n) :
    parafermionicCoverBoxOriginConnectionWeight n q v.1 =
      ((law (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
        {A | ActualConnected (ParafermionicAmbientGraph n) A
          (parafermionicCoverBoxOrigin n) v}).toReal := by
  simp [parafermionicCoverBoxOriginConnectionWeight]

end
end PottsContinuity.FKC.FiniteFK
