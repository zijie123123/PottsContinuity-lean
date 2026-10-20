module

public import PottsContinuity.Thm4.FKCProbabilityBridge
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK Filter Topology
noncomputable section
local instance {V : Type*} [Finite V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- The explicit self-dual edge probability is continuous for real q >= 1. -/
theorem continuous_selfDual_edgeProbability :
    Continuous (fun q : Set.Ici (1 : ℝ) => (selfDualParameters q).edgeProbability.val) := by
  change Continuous (fun q : Set.Ici (1 : ℝ) => Real.sqrt q.val / (1 + Real.sqrt q.val))
  exact (Real.continuous_sqrt.comp continuous_subtype_val).div
    (continuous_const.add (Real.continuous_sqrt.comp continuous_subtype_val))
    (fun q => ne_of_gt (by positivity))

/-- Actual finite FK weights vary continuously along the self-dual curve. -/
theorem continuous_selfDual_weight {V : Type*} [Finite V] (G : SimpleGraph V)
    (ξ : BoundaryCondition V) (A : Configuration G) :
    Continuous (fun q : Set.Ici (1 : ℝ) => weight G (selfDualParameters q) ξ A) := by
  change Continuous (fun q : Set.Ici (1 : ℝ) =>
    (selfDualParameters q).edgeProbability.val ^ A.card *
      (1 - (selfDualParameters q).edgeProbability.val) ^
        (Nat.card G.edgeSet - A.card) * q.val ^ componentCount G ξ A)
  exact ((continuous_selfDual_edgeProbability.pow _).mul
    ((continuous_const.sub continuous_selfDual_edgeProbability).pow _)).mul
      (continuous_subtype_val.pow _)

theorem continuous_selfDual_partitionFunction {V : Type*} [Finite V] (G : SimpleGraph V)
    (ξ : BoundaryCondition V) :
    Continuous (fun q : Set.Ici (1 : ℝ) => partitionFunction G (selfDualParameters q) ξ) := by
  unfold partitionFunction FiniteProbability.partition
  exact continuous_finsetSum _ (fun A _ => continuous_selfDual_weight G ξ A)

theorem continuous_selfDual_configurationProbability {V : Type*} [Finite V]
    (G : SimpleGraph V) (ξ : BoundaryCondition V) (A : Configuration G) :
    Continuous (fun q : Set.Ici (1 : ℝ) =>
      configurationProbability G (selfDualParameters q) ξ A) := by
  unfold configurationProbability
  exact (continuous_selfDual_weight G ξ A).div
    (continuous_selfDual_partitionFunction G ξ)
    (fun q => ne_of_gt (partitionFunction_pos G (selfDualParameters q) ξ))

/-- Every fixed event has continuous actual finite free/wired/mixed FK probability.
The event is independent of q; arbitrary boundary partitions are permitted. -/
theorem continuous_selfDual_eventProbability {V : Type*} [Finite V]
    (G : SimpleGraph V) (ξ : BoundaryCondition V) (s : Set (Configuration G)) :
    Continuous (fun q : Set.Ici (1 : ℝ) => (measure G (selfDualParameters q) ξ s).toReal) := by
  classical
  have heq : (fun q : Set.Ici (1 : ℝ) => (measure G (selfDualParameters q) ξ s).toReal) =
      fun q : Set.Ici (1 : ℝ) =>
        ∑ A : Configuration G, configurationProbability G (selfDualParameters q) ξ A *
          s.indicator (fun _ => (1 : ℝ)) A := by
    funext q
    exact measure_toReal_eq_indicator_sum (G := G) (selfDualParameters q) ξ s
  rw [heq]
  exact continuous_finsetSum _ (fun A _ =>
    (continuous_selfDual_configurationProbability G ξ A).mul continuous_const)

end
end PottsContinuity.Thm4
