module

public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.FK.FiniteProbability
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance mixedEmbeddedLowerInnerFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance mixedEmbeddedLowerOuterEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

private theorem mixedEmbedded_indicator_expectation {V : Type*} [Finite V]
    (G : SimpleGraph V) (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal = expectation (law G q ξ) (S.indicator (fun _ => (1:ℝ))) := by
  classical
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr rfl
  intro A _
  by_cases h : A ∈ S
  · simp [Set.indicator,h,law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
  · simp [Set.indicator,h]

/-- A finite larger graph dominates every increasing original-edge event
when its original boundary already dominates the embedded inner boundary.
All exterior-state comparisons and mixture normalization are proved. -/
theorem embedded_measure_lower_of_boundary_domination
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (q : Parameters) (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (hpart : η.partition ≤ (isolatedExtensionPullbackBoundary f ξ).partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure G q η S).toReal ≤
      (measure H q ξ {C | embeddedConfigurationRestriction G H f hGH C ∈ S}).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  let marg := frozenMarginalLaw q ξ R
  let cond : RemovedConfiguration H R → PMF (Configuration G) := fun K =>
    law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
  let restr := embeddedConfigurationRestriction G H f hGH
  let ind : Configuration G → ℝ := S.indicator (fun _ => (1:ℝ))
  have hmix : (law H q ξ).map restr = marg.bind cond :=
    law_embeddedConfigurationRestriction_eq_bind_frozenMarginal G H f hGH q ξ
  have hconditional : ∀ K : RemovedConfiguration H R,
      expectation (law G q η) ind ≤ expectation (cond K) ind := by
    intro K
    have hηK : η.partition ≤
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition := by
      intro u v huv
      change (componentSetoid H ξ K.val).r (f u) (f v)
      exact boundary_component H ξ K.val (hpart huv)
    have hh := measure_boundary_comparison (G := G) q η
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) hηK S hS
    simpa only [mixedEmbedded_indicator_expectation,cond,ind] using hh
  have havg := le_expectation_bind marg cond ind (expectation (law G q η) ind) hconditional
  rw [← hmix] at havg
  rw [expectation_map] at havg
  rw [mixedEmbedded_indicator_expectation G q η S,
    mixedEmbedded_indicator_expectation H q ξ _]
  exact havg

end
end PottsContinuity.PlanarMixed
