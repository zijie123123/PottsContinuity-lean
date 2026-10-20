module

public import PottsContinuity.Thm3.Prop4.FrozenLowerMonotonicity
public import PottsContinuity.PD.FK.Disintegration
public import PottsContinuity.PD.FK.ProbabilityProduct
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Disintegration of the entire original configuration

The fixed revealed-state marginal and its normalized conditional fiber
reconstruct the original PMF, including every revealed edge.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance originalDisintegrationEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Exact joint disintegration of the remaining and revealed configurations. -/
theorem finite_FK_split_law_eq_frozen_mixture {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ : BoundaryCondition V) (R : Configuration G) :
    (law G θ ξ).map (configurationSplitEquiv G R) =
      (frozenMarginalLaw θ ξ R).bind (fun H =>
        (frozenFiberLaw θ ξ R H).map (fun A => (A,H))) := by
  classical
  let : Fintype (RemovedConfiguration G R) := Fintype.ofFinite _
  let : Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
  ext z
  rcases z with ⟨A,H⟩
  rw [FiniteProbability.map_equiv_apply]
  change law G θ ξ (A.val ∪ H.val) = _
  rw [law_restore_eq_conditional_mul_marginal]
  simp only [PMF.bind_apply,PMF.map_apply,tsum_fintype,Prod.mk.injEq]
  simp only [ite_and,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [frozenFiberLaw_eq_remainingLaw,mul_comm]

/-- Restoring the conditional sample after drawing the actual frozen marginal
gives the complete original finite FK PMF. -/
theorem finite_FK_original_law_eq_frozen_mixture {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ : BoundaryCondition V) (R : Configuration G) :
    law G θ ξ = (frozenMarginalLaw θ ξ R).bind (fun H =>
      (frozenFiberLaw θ ξ R H).map (fun A => A.val ∪ H.val)) := by
  have h := congrArg (fun p => p.map (configurationSplitEquiv G R).symm)
    (finite_FK_split_law_eq_frozen_mixture G θ ξ R)
  rw [PMF.map_comp] at h
  simp only [Equiv.symm_comp_self,PMF.map_id] at h
  rw [PMF.map_bind] at h
  simp only [PMF.map_comp] at h
  exact h

/-- Every event is averaged with its actual frozen-state marginal and its
normalized conditional probability in the full restored sample. -/
theorem finite_FK_event_eq_frozen_mixture {V : Type*} [Finite V] (G : SimpleGraph V)
    (θ : Parameters) (ξ : BoundaryCondition V) (R : Configuration G)
    (E : Set (Configuration G)) :
    measure G θ ξ E = ∑' H : RemovedConfiguration G R,
      frozenMarginalLaw θ ξ R H *
        (frozenFiberLaw θ ξ R H).toMeasure {A | A.val ∪ H.val ∈ E} := by
  change (law G θ ξ).toMeasure E = _
  rw [finite_FK_original_law_eq_frozen_mixture G θ ξ R,
    PMF.toMeasure_bind_apply _ _ E MeasurableSpace.measurableSet_top]
  apply tsum_congr
  intro H
  rw [PMF.toMeasure_map_apply]
  · rfl
  · exact fun _ _ => MeasurableSpace.measurableSet_top
  · exact MeasurableSpace.measurableSet_top

end
end PottsContinuity.Thm3.Prop4
