module

public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Uniform conditional target bounds after actual-cluster exploration -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterConditionalEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- The free induced law, extended by closed original edges, is below the
ambient free law on every increasing event. -/
theorem free_induced_extension_probability_le (θ : Parameters) (C : Set V)
    (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure (G.induce C) θ (BoundaryCondition.free ∅)
      {B | RSW.inducedConfigurationExtension C B ∈ E}).toReal ≤
    (measure G θ (BoundaryCondition.free ∅) E).toReal := by
  have h := RSW.embedded_free_probability_le (G.induce C) G (RSW.inducedVertexEmbedding C)
    (RSW.inducedVertexEmbedding_map_le C) θ
    {B | RSW.inducedConfigurationExtension C B ∈ E}
    (hE.preimage (RSW.inducedConfigurationExtension_monotone C))
  apply h.trans (measureReal_mono _ (measure_ne_top _ _))
  intro A hA
  exact hE (RSW.inducedConfigurationErasure_subset C A) hA

/-- On every attained cluster record, the second root's target event together
with disconnection from the first root costs at most its ambient free marginal. -/
theorem clusterRecord_target_disconnected_probability_le (θ : Parameters)
    (u v : V) (T : Set V) (A₀ : Configuration G) :
    (((law G θ (BoundaryCondition.free ∅)).filter
      (Exploration.revealRecordEvent (clusterReveal G u) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (clusterReveal G u) (clusterReveal_stable G u) A₀]
        exact frozenStateEvent_support θ (BoundaryCondition.free ∅) (clusterReveal G u A₀)
          (Exploration.revealRecordConfiguration (clusterReveal G u) A₀))).toMeasure
      (targetConnectionEvent v T ∩ {A | ¬ ActualConnected G A u v})).toReal ≤
    (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent v T)).toReal := by
  classical
  let ξ := BoundaryCondition.free (∅ : Set V)
  let reveal := clusterReveal G u
  let hs : ∃ A ∈ Exploration.revealRecordEvent reveal A₀, A ∈ (law G θ ξ).support := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal (clusterReveal_stable G u) A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (Exploration.revealRecordEvent reveal A₀) hs
  let C := clusterComplement u A₀
  let E := targetConnectionEvent (G := G) v T
  let S : Set (Configuration (G.induce C)) := {B | RSW.inducedConfigurationExtension C B ∈ E}
  have hmap := congrArg (fun p : PMF (Configuration (G.induce C)) => p.toMeasure S)
    (law_filter_clusterRecord_map_complement_free θ u A₀)
  change (ρ.map (RSW.inducedConfigurationRestriction C)).toMeasure S =
    measure (G.induce C) θ (BoundaryCondition.free ∅) S at hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hmap
  have hsub : ρ.toMeasure (E ∩ {A | ¬ ActualConnected G A u v}) ≤
      ρ.toMeasure {A | RSW.inducedConfigurationRestriction C A ∈ S} := by
    apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
    intro A hA
    have hr := ((PMF.mem_support_filter_iff hs).mp hA.2).1
    have hv : v ∈ clusterComplement u A₀ := by
      intro hconn
      exact hA.1.2 ((clusterConnected_iff_of_reveal_agreement G u A₀ A hr.2 v).mpr hconn)
    exact targetConnection_survives_clusterRecord u v T A₀ A hr hv hA.1.1
  change (ρ.toMeasure (E ∩ {A | ¬ ActualConnected G A u v})).toReal ≤ _
  calc
    _ ≤ (ρ.toMeasure {A | RSW.inducedConfigurationRestriction C A ∈ S}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hsub
    _ = (measure (G.induce C) θ (BoundaryCondition.free ∅) S).toReal :=
      congrArg ENNReal.toReal hmap
    _ ≤ _ := free_induced_extension_probability_le θ C E (targetConnectionEvent_upper v T)

end
end PottsContinuity.Thm3.Prop4
