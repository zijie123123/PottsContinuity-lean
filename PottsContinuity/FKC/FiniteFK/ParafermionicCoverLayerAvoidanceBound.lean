-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverLayerAvoidanceBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerConditionalBound
public import PottsContinuity.FKC.FiniteFK.DisjointBlockEventAvoidance
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverIntermediateLayers
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

local instance layerAvoidAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance layerAvoidAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _
local instance layerAvoidConfigurationMeasurableSpace (n : ℕ) :
    MeasurableSpace (Configuration (ParafermionicAmbientGraph n)) := ⊤
local instance layerAvoidConfigurationMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Configuration (ParafermionicAmbientGraph n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Avoiding every actual branch-root event in a finite set of distinct cover
layers has the product bound obtained from their disjoint original-edge
supports and the uniform conditional branch-root estimate. -/
theorem parafermionicCoverLayerBranchRootAvoidance_probability_bound
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (J : Finset (ParafermionicCoverLayerIndex n)) :
    ((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).toMeasure
      (disjointBlockAvoidanceSet
        (fun k => parafermionicCoverLayerBranchRootEvent n k.1 k.2 hn) J)).toReal ≤
      (1 - 1 / (60 * (n : ℝ)^4)) ^ J.card := by
  classical
  let H := ParafermionicAmbientGraph n
  let E : ParafermionicCoverLayerIndex n → Set (Configuration H) :=
    fun k => parafermionicCoverLayerBranchRootEvent n k.1 k.2 hn
  let F : ParafermionicCoverLayerIndex n → Finset H.edgeSet :=
    fun k => parafermionicCoverLayerBlock n k.1 k.2
  let c : ParafermionicCoverLayerIndex n → ℝ := fun _ => 1 / (60 * (n : ℝ)^4)
  have hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
    intro i j hij
    exact parafermionicCoverLayerBlock_disjoint n i.1 j.1 i.2 j.2 (by
      intro h
      exact hij (Subtype.ext h))
  have hlocal : ∀ i A B, A ∩ F i = B ∩ F i → (A ∈ E i ↔ B ∈ E i) := by
    intro i A B hAB
    exact parafermionicCoverLayerBranchRootEvent_local n i.1 i.2 hn A B hAB
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    dsimp [c]
    positivity
  have hc1 : ∀ i, c i ≤ 1 := by
    intro i
    dsimp [c]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn4 : (1 : ℝ) ≤ (n : ℝ)^4 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ)^2 - 1)]
    have hden : (1 : ℝ) ≤ 60 * (n : ℝ)^4 := by nlinarith [hn4]
    rw [div_le_one (by positivity : (0 : ℝ) < 60 * (n : ℝ)^4)]
    exact hden
  have hcond : ∀ i (y : Set.range (fun A : Finset H.edgeSet => A \ F i)),
      c i ≤ ((finiteStatisticConditionalPMF
        (law H q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))))
        (fun A => (law_pos H q (BoundaryCondition.free ∅) A).ne')
        (fun A : Finset H.edgeSet => A \ F i) y).toMeasure (E i)).toReal := by
    intro i y
    dsimp [c, E, H, F]
    exact parafermionicCoverLayerBranchRootEvent_conditional_ge_polynomial
      n hn i.1 i.2 q y
  simpa [H, E, F, c, disjointBlockAvoidanceSet] using
    (disjointBlock_event_avoidance_bound
      (p := law H q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))))
      (hp := fun A => (law_pos H q (BoundaryCondition.free ∅) A).ne')
      F E J c hdisj hlocal hc0 hc1 hcond)

end
end PottsContinuity.FKC.FiniteFK
