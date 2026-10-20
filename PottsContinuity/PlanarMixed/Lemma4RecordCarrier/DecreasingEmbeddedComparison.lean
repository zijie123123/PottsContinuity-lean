module

public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- For a decreasing event the boundary comparison has the reverse direction. -/
theorem finite_decreasing_boundary_comparison {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (S : Set (Configuration G)) (hS : IsLowerSet S) :
    (measure G θ η S).toReal ≤ (measure G θ ξ S).toReal := by
  have h := measure_boundary_comparison (G := G) θ ξ η hξη Sᶜ hS.compl
  change (measure G θ ξ).real Sᶜ ≤ (measure G θ η).real Sᶜ at h
  rw [probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet S),
    probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet S)] at h
  change (measure G θ η).real S ≤ (measure G θ ξ).real S
  linarith

/-- A dominating induced partition gives a lower comparison for decreasing
local events under every exterior configuration. -/
theorem embedded_decreasing_comparison_of_frozen_partition
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (hGH : G.map f ≤ H) (θ : Parameters) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V) (S : Set (Configuration G)) (hS : IsLowerSet S)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition) :
    (measure G θ η S).toReal ≤
      (measure H θ ξ {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal := by
  have h := embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    G H f hGH θ ξ η Sᶜ hS.compl hpart
  have heq : {A | embeddedConfigurationRestriction G H f hGH A ∈ Sᶜ} =
      {A | embeddedConfigurationRestriction G H f hGH A ∈ S}ᶜ := rfl
  rw [heq] at h
  change (measure H θ ξ).real _ᶜ ≤ (measure G θ η).real Sᶜ at h
  rw [probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet _),
    probReal_compl_eq_one_sub (MeasurableSpace.measurableSet_top : MeasurableSet S)] at h
  change (measure G θ η).real S ≤ (measure H θ ξ).real _
  linarith

/-- Open exterior edges attach to the retained graph only on the marked
side vertices. All other exterior vertices may be identified arbitrarily. -/
theorem frozen_free_partition_le_wired_of_endpoint_attachment
    {V W : Type*} (H : SimpleGraph W) (f : V ↪ W) (B : Set V)
    (K : Configuration H)
    (hattach : ∀ e ∈ K, ∀ v, f v ∈ e.val → v ∈ B) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary (BoundaryCondition.free ∅) K)).partition ≤
      (BoundaryCondition.wired B).partition := by
  let D : Set W := {w | ∀ v, f v=w → v ∈ B}
  have hbound : (frozenBoundary (BoundaryCondition.free ∅) K).partition ≤
      (BoundaryCondition.wired D).partition := by
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      obtain ⟨e,he,heq⟩ := (openGraph_adj H K x y).mp hxy
      apply (BoundaryCondition.wired_rel D x y).mpr
      right
      constructor
      · intro v hv
        exact hattach e he v (by rw [hv,heq]; exact Sym2.mem_mk_left _ _)
      · intro v hv
        exact hattach e he v (by rw [hv,heq]; exact Sym2.mem_mk_right _ _)
    · exact bot_le
  intro u v huv
  have h := hbound huv
  rcases (BoundaryCondition.wired_rel D (f u) (f v)).mp h with h | ⟨hu,hv⟩
  · exact Or.inl (f.injective h)
  · exact Or.inr ⟨hu u rfl,hv v rfl⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
