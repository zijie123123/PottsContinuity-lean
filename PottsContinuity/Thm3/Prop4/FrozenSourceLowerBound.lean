module

public import PottsContinuity.Thm3.Prop4.FrozenOriginalDisintegration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Averaging a decreasing event over a fixed revealed source event

Any event determined by the revealed edge state admits the same all-open
reference lower bound. The source event need not be monotone.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance frozenSourceEdgeDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _
local instance frozenSourceRemovedMeasurableSpace (V : Finset LatticeVertex)
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    MeasurableSpace (RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R) := ⊤

/-- The actual all-open reference probability bounds the conditional lower
event uniformly after restricting to any event of the fixed revealed state. -/
theorem finite_FK_lower_event_joint_ge_all_open (V : Finset LatticeVertex)
    (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (S : Set (RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R))
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex))))
    (hE : IsLowerSet E) :
    (frozenFiberLaw θ ξ R ⟨R,Finset.Subset.refl R⟩).toMeasure {A | A.val ∪ R ∈ E} *
      measure _ θ ξ {C | (configurationSplitEquiv _ R C).2 ∈ S} ≤
    measure _ θ ξ ({C | (configurationSplitEquiv _ R C).2 ∈ S} ∩ E) := by
  let G := squareLattice.induce (V : Set LatticeVertex)
  let c := (frozenFiberLaw θ ξ R ⟨R,Finset.Subset.refl R⟩).toMeasure {A | A.val ∪ R ∈ E}
  have hsource : measure G θ ξ {C | (configurationSplitEquiv G R C).2 ∈ S} =
      (frozenMarginalLaw θ ξ R).toMeasure S := by
    symm
    unfold frozenMarginalLaw
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact fun _ _ => MeasurableSpace.measurableSet_top
    · exact MeasurableSpace.measurableSet_top
  change c * measure G θ ξ _ ≤ measure G θ ξ _
  rw [hsource,finite_FK_event_eq_frozen_mixture G θ ξ R,
    PMF.toMeasure_apply _ MeasurableSpace.measurableSet_top,← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro H
  have hsplit (A : RemainingConfiguration G R) :
      configurationSplitEquiv G R (A.val ∪ H.val) = (A,H) :=
    (configurationSplitEquiv G R).apply_symm_apply (A,H)
  by_cases hH : H ∈ S
  · simp only [Set.indicator_of_mem hH]
    have heq : {A : RemainingConfiguration G R |
        A.val ∪ H.val ∈ ({C | (configurationSplitEquiv G R C).2 ∈ S} ∩ E)} =
        {A | A.val ∪ H.val ∈ E} := by
      ext A
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,hsplit,hH,true_and]
    rw [heq,mul_comm c]
    exact mul_le_mul' le_rfl
      ((ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (frozen_fiber_lower_event_ge_all_open V θ ξ R H E hE))
  · simp only [Set.indicator_of_notMem hH,mul_zero,zero_le]

end
end PottsContinuity.Thm3.Prop4
