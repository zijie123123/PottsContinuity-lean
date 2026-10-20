module

public import PottsContinuity.PD.FK.ConditionalLaw
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance frozenRestoreEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The probability of any original sampled event on an exact frozen fibre
is its remaining-edge probability after restoring the recorded open bonds. -/
theorem frozen_event_probability_eq_restored_remaining
    {V : Type*} [Finite V] (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G) (K : RemovedConfiguration G R)
    (E : Set (Configuration G)) :
    (((law G θ ξ).filter (frozenStateEvent R K)
      (frozenStateEvent_support θ ξ R K)).toMeasure E) =
    (remainingLaw G θ (frozenBoundary ξ K.val) R).toMeasure
      {A | A.val ∪ K.val ∈ E} := by
  let Q := (law G θ ξ).filter (frozenStateEvent R K)
    (frozenStateEvent_support θ ξ R K)
  let f := fun C => (configurationSplitEquiv G R C).1
  let D : Set (RemainingConfiguration G R) := {A | A.val ∪ K.val ∈ E}
  have hrest (C : Configuration G) (hC : C ∈ Q.support) :
      (f C).val ∪ K.val = C := by
    have hk := ((PMF.mem_support_filter_iff (frozenStateEvent_support θ ξ R K)).mp hC).1
    change C ∩ R = K.val at hk
    have h := (configurationSplitEquiv G R).symm_apply_apply C
    change (f C).val ∪ (C ∩ R) = C at h
    rw [hk] at h
    exact h
  have hprob : Q.toMeasure E = Q.toMeasure (f ⁻¹' D) := by
    apply PMF.toMeasure_apply_eq_of_inter_support_eq _
      MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
    ext C
    constructor
    · rintro ⟨hE,hC⟩
      exact ⟨by change (f C).val ∪ K.val ∈ E; rw [hrest C hC]; exact hE,hC⟩
    · rintro ⟨hE,hC⟩
      change (f C).val ∪ K.val ∈ E at hE
      exact ⟨by rwa [hrest C hC] at hE,hC⟩
  calc
    Q.toMeasure E = Q.toMeasure (f ⁻¹' D) := hprob
    _ = (Q.map f).toMeasure D := by
      rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
    _ = _ := congrArg (fun p : PMF (RemainingConfiguration G R) => p.toMeasure D)
      (law_filter_frozen_map_remaining θ ξ R K)

end
end PottsContinuity.RSW
