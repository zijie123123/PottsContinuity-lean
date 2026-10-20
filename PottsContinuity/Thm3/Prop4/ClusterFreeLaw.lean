module

public import PottsContinuity.Thm3.Prop4.ClusterComplement
public import PottsContinuity.Thm3.Prop4.ExteriorPartition
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Free law outside the actual revealed seed cluster

All open recorded edges have both endpoints in the removed cluster.
Consequently the induced complement inherits a genuinely free partition.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterFreeEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
/-- Two endpoints of an actual open edge are actually connected. -/
theorem connected_of_open_edge_endpoints (A : Configuration G) {e : G.edgeSet}
    (he : e ∈ A) {x y : V} (hx : x ∈ e.val) (hy : y ∈ e.val) :
    ActualConnected G A x y := by
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
  have hopen : (openGraph G A).Adj a b := (openGraph_adj G A a b).mpr ⟨e,he,hab.symm⟩
  have hx' : x = a ∨ x = b := by rw [← hab] at hx; exact Sym2.mem_iff'.mp hx
  have hy' : y = a ∨ y = b := by rw [← hab] at hy; exact Sym2.mem_iff'.mp hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hopen.reachable
  · exact hopen.reachable.symm
  · exact SimpleGraph.Reachable.refl _

/-- Every open edge recorded in the seed-cluster exploration has both endpoints in that cluster. -/
theorem clusterRecord_open_endpoint_connected (u : V) (A₀ : Configuration G)
    {e : G.edgeSet}
    (he : e ∈ (Exploration.revealRecordConfiguration (clusterReveal G u) A₀).val)
    {x : V} (hx : x ∈ e.val) : ActualConnected G A₀ u x := by
  have heA : e ∈ A₀ := (Finset.mem_inter.mp he).1
  obtain ⟨y,hy,huy⟩ := (clusterReveal_mem_iff G u A₀ e).mp (Finset.mem_inter.mp he).2
  exact huy.trans (connected_of_open_edge_endpoints A₀ heA hy hx)

/-- Pullback to the actual complement of the frozen free boundary is discrete. -/
theorem clusterComplement_frozen_free_partition (u : V) (A₀ : Configuration G) :
    (isolatedExtensionPullbackBoundary (clusterComplementEmbedding u A₀)
      (frozenBoundary (BoundaryCondition.free ∅)
        (Exploration.revealRecordConfiguration (clusterReveal G u) A₀).val)).partition =
      (BoundaryCondition.free ∅).partition := by
  apply Setoid.ext
  intro a b
  change (componentSetoid G (BoundaryCondition.free ∅)
    (Exploration.revealRecordConfiguration (clusterReveal G u) A₀).val).r a.val b.val ↔ a=b
  constructor
  · intro hab
    have hlarge := componentSetoid_le_wired_union_of_edge_endpoints
      (BoundaryCondition.free (∅ : Set V)) {x | ActualConnected G A₀ u x}
      (Exploration.revealRecordConfiguration (clusterReveal G u) A₀).val
      (fun _ he _ hx => clusterRecord_open_endpoint_connected u A₀ he hx) hab
    rcases (BoundaryCondition.wired_rel _ a.val b.val).mp hlarge with heq | ⟨ha,hb⟩
    · exact Subtype.ext heq
    · have hconn : ActualConnected G A₀ u a.val := by simpa [BoundaryCondition.free] using ha
      exact False.elim (a.property hconn)
  · rintro rfl
    exact (componentSetoid G _ _).refl _

/-- The exact stopped complement law is free, not merely dominated by a free law. -/
theorem law_filter_clusterRecord_map_complement_free (θ : Parameters)
    (u : V) (A₀ : Configuration G) :
    ((law G θ (BoundaryCondition.free ∅)).filter
      (Exploration.revealRecordEvent (clusterReveal G u) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (clusterReveal G u) (clusterReveal_stable G u) A₀]
        exact frozenStateEvent_support θ (BoundaryCondition.free ∅) (clusterReveal G u A₀)
          (Exploration.revealRecordConfiguration (clusterReveal G u) A₀))).map
      (embeddedConfigurationRestriction (G.induce (clusterComplement u A₀)) G
        (clusterComplementEmbedding u A₀) (clusterComplement_map_le u A₀)) =
    law (G.induce (clusterComplement u A₀)) θ (BoundaryCondition.free ∅) := by
  rw [law_filter_clusterRecord_map_complement]
  apply law_eq_of_boundary_partition_eq
  exact clusterComplement_frozen_free_partition u A₀

end
end PottsContinuity.Thm3.Prop4
