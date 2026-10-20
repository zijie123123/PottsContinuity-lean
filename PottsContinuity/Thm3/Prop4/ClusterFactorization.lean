module

public import PottsContinuity.Thm3.Prop4.ClusterConditional
public import PottsContinuity.Thm3.RSW.StoppingJointUpper

/-!
# Free product bound for genuinely different open clusters

The first root's target event is measurable in its actual cluster record.
The second cluster's target event has its free marginal bound on every such
record. Averaging gives the upper product without an independence assumption.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterFactorEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Actual target connections in different open clusters have the upper product
of their ambient free marginals, at every independent FK parameter. -/
theorem free_disconnected_target_product (θ : Parameters) (u v : V) (S T : Set V) :
    (measure G θ (BoundaryCondition.free ∅)
      {A | A ∈ targetConnectionEvent u S ∧ A ∈ targetConnectionEvent v T ∧
        ¬ ActualConnected G A u v}).toReal ≤
      (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent u S)).toReal *
      (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent v T)).toReal := by
  have h := RSW.stopped_event_inter_upper_of_record_bounds θ (BoundaryCondition.free ∅)
    (clusterReveal G u) (clusterReveal_stable G u)
    (targetConnectionEvent v T ∩ {A | ¬ ActualConnected G A u v})
    (targetConnectionEvent u S)
    (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent v T)).toReal
    (fun A₀ A hr => targetConnectionEvent_clusterRecord_iff u S A₀ A hr)
    (fun A₀ => clusterRecord_target_disconnected_probability_le θ u v T A₀)
  have hset :
      (targetConnectionEvent v T ∩ {A | ¬ ActualConnected G A u v}) ∩ targetConnectionEvent u S =
      {A | A ∈ targetConnectionEvent u S ∧ A ∈ targetConnectionEvent v T ∧
        ¬ ActualConnected G A u v} := by ext A; simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]; tauto
  rw [hset,mul_comm] at h
  exact h

/-- An explicit separation interface suffices for any smaller geometric event;
this conditional consumer is not exported as a proved planar separation theorem. -/
theorem free_target_product_of_cluster_separation (θ : Parameters) (u v : V) (S T : Set V)
    (F : Set (Configuration G)) (hseparation : ∀ A ∈ F, ¬ ActualConnected G A u v) :
    (measure G θ (BoundaryCondition.free ∅)
      (F ∩ targetConnectionEvent u S ∩ targetConnectionEvent v T)).toReal ≤
      (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent u S)).toReal *
      (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent v T)).toReal := by
  apply (measureReal_mono _ (measure_ne_top _ _)).trans (free_disconnected_target_product θ u v S T)
  rintro A ⟨⟨hF,hS⟩,hT⟩
  exact ⟨hS,hT,hseparation A hF⟩

end
end PottsContinuity.Thm3.Prop4
