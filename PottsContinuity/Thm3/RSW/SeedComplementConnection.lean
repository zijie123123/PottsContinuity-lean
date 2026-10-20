module

public import PottsContinuity.Thm3.RSW.SeedComplementLaw
public import PottsContinuity.FKC.FiniteFK.BoundarySeedComplementConnectivity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Actual connections under the all-boundary-seed exploration

Connections between unexposed vertices remain actual connections in the induced
complement. In combination with SeedComplementLaw this gives an exact free
conditional connection probability for every real q ≥ 1. No planar separation
or virtual boundary connection is used.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedComplementConnectionVertexFintype : Fintype V := Fintype.ofFinite V
local instance seedComplementConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- An actual connection on an attained boundary-seed record is precisely an
actual connection in its induced complement. -/
theorem boundarySeedComplement_connection_iff_allq
    (ξ : BoundaryCondition V) (A₀ B : Configuration G)
    (hrecord : B ∈ revealRecordEvent
      (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset) A₀)
    (x y : FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀) :
    ActualConnected G B x.val y.val ↔
      ActualConnected
        (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀))
        (embeddedConfigurationRestriction
          (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀)) G
          (FKC.FiniteFK.wiredAvoidingComplementEmbedding G ∅ ξ.boundary.toFinset A₀)
          (FKC.FiniteFK.wiredAvoidingComplementGraph_le (G := G) ∅ ξ.boundary.toFinset A₀) B)
        x y := by
  let ξ' : FKC.FiniteFK.BoundaryCondition V := ⟨ξ.boundary, ξ.partition, ξ.supported⟩
  exact FKC.FiniteFK.boundarySeedComplement_actualConnected_iff_of_record
    ξ' A₀ B hrecord

/-- The exact free conditional probability of an actual connection whose
endpoints lie in the unexposed complement of the boundary-seed clusters. -/
theorem boundarySeedRecord_connection_probability_allq
    (θ : Parameters) (ξ : BoundaryCondition V) (A₀ : Configuration G)
    (x y : FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀) :
    (((law G θ ξ).filter
      (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent
          (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset)
          (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
            (∅ : Set V) ξ.boundary.toFinset A B h) A₀]
        exact frozenStateEvent_support θ ξ _ _)).toMeasure
          {B | ActualConnected G B x.val y.val}) =
      measure (G.induce (FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀))
        θ (BoundaryCondition.free ∅) {B | ActualConnected _ B x y} := by
  let reveal := FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ ξ.boundary.toFinset
  let hs : ∃ B ∈ revealRecordEvent reveal A₀, B ∈ (law G θ ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal
      (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
        (∅ : Set V) ξ.boundary.toFinset A B h) A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (revealRecordEvent reveal A₀) hs
  let C := FKC.FiniteFK.wiredAvoidingComplementSet G ∅ ξ.boundary.toFinset A₀
  let restrict := embeddedConfigurationRestriction (G.induce C) G
    (FKC.FiniteFK.wiredAvoidingComplementEmbedding G ∅ ξ.boundary.toFinset A₀)
    (FKC.FiniteFK.wiredAvoidingComplementGraph_le (G := G) ∅ ξ.boundary.toFinset A₀)
  have heq : ρ.toMeasure {B | ActualConnected G B x.val y.val} =
      ρ.toMeasure (restrict ⁻¹' {B | ActualConnected (G.induce C) B x y}) := by
    apply PMF.toMeasure_apply_eq_of_inter_support_eq _
      MeasurableSpace.measurableSet_top MeasurableSpace.measurableSet_top
    ext B
    have hiff (hB : B ∈ ρ.support) :=
      boundarySeedComplement_connection_iff_allq ξ A₀ B
        ((PMF.mem_support_filter_iff hs).mp hB).1 x y
    exact ⟨fun ⟨h, hB⟩ => ⟨(hiff hB).mp h, hB⟩,
      fun ⟨h, hB⟩ => ⟨(hiff hB).mpr h, hB⟩⟩
  have hmap := congrArg (fun p : PMF (Configuration (G.induce C)) =>
    p.toMeasure {B | ActualConnected (G.induce C) B x y})
    (law_filter_boundarySeedRecord_map_complement_eq_free_allq θ ξ A₀)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at hmap
  exact heq.trans hmap

end
end PottsContinuity.RSW
