-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverConnectionProbability.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConnectionAvoidance
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerAvoidanceBound
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerDecay
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverIntermediateLayers
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

local instance coverConnectionConfigurationMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance coverConnectionConfigurationMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The free finite FK probability of an actual cover connection is bounded by
the finite-layer avoidance estimate whenever all indexed layers separate its
endpoints. -/
theorem parafermionicCoverConnection_probability_le_avoidance
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (J : Finset (ParafermionicCoverLayerIndex n))
    {u v : ParafermionicAmbientVertex n}
    (hstraddle : ∀ i ∈ J,
      ((u.val.2 < i.val ∧ i.val < v.val.2) ∨
        (v.val.2 < i.val ∧ i.val < u.val.2))) :
    ((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      {A | ActualConnected (ParafermionicAmbientGraph n) A u v}).toReal ≤
      (1 - 1 / (60 * (n : ℝ)^4)) ^ J.card := by
  let μ := (law (ParafermionicAmbientGraph n) q
    (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
  have hsubset :
      {A : Configuration (ParafermionicAmbientGraph n) |
        ActualConnected (ParafermionicAmbientGraph n) A u v} ⊆
      disjointBlockAvoidanceSet
        (fun i : ParafermionicCoverLayerIndex n =>
          parafermionicCoverLayerBranchRootEvent n i.val i.property hn) J :=
    parafermionicCoverConnection_avoids_straddledLayerBranchRootEvents n hn J hstraddle
  have hmeasure := MeasureTheory.measure_mono (μ := μ) hsubset
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
  simpa [μ] using hreal.trans
    (parafermionicCoverLayerBranchRootAvoidance_probability_bound n hn q J)

/-- A connection from sheet zero to the positive extremal sheet has an
exponentially small actual free finite-FK probability. -/
theorem parafermionicCoverConnection_probability_le_exp_positive
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    {u v : ParafermionicAmbientVertex n}
    (hu : u.val.2 = 0)
    (hv : v.val.2 = ((n ^ 5 : ℕ) : ℤ)) :
    ((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      {A | ActualConnected (ParafermionicAmbientGraph n) A u v}).toReal ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  have hstraddle : ∀ i ∈ parafermionicCoverPositiveIntermediateLayers n,
      u.val.2 < i.val ∧ i.val < v.val.2 := by
    intro i hi
    have hmem := (mem_parafermionicCoverPositiveIntermediateLayers n i).mp hi
    rw [hu, hv]
    exact hmem
  have hbound := parafermionicCoverConnection_probability_le_avoidance
    n hn q (parafermionicCoverPositiveIntermediateLayers n)
      (fun i hi => Or.inl (hstraddle i hi))
  rw [card_parafermionicCoverPositiveIntermediateLayers n hn] at hbound
  exact hbound.trans (parafermionicCoverLayerDecay n hn)

/-- A connection from sheet zero to the negative extremal sheet has an
exponentially small actual free finite-FK probability. -/
theorem parafermionicCoverConnection_probability_le_exp_negative
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    {u v : ParafermionicAmbientVertex n}
    (hu : u.val.2 = 0)
    (hv : v.val.2 = -((n ^ 5 : ℕ) : ℤ)) :
    ((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      {A | ActualConnected (ParafermionicAmbientGraph n) A u v}).toReal ≤
      Real.exp (-((n : ℝ) - 1) / 60) := by
  have hstraddle : ∀ i ∈ parafermionicCoverNegativeIntermediateLayers n,
      v.val.2 < i.val ∧ i.val < u.val.2 := by
    intro i hi
    have hmem := (mem_parafermionicCoverNegativeIntermediateLayers n i).mp hi
    rw [hu, hv]
    exact hmem
  have hbound := parafermionicCoverConnection_probability_le_avoidance
    n hn q (parafermionicCoverNegativeIntermediateLayers n)
      (fun i hi => Or.inr (hstraddle i hi))
  rw [card_parafermionicCoverNegativeIntermediateLayers n hn] at hbound
  exact hbound.trans (parafermionicCoverLayerDecay n hn)

end PottsContinuity.FKC.FiniteFK
