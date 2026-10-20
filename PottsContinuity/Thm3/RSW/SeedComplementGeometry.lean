module

public import PottsContinuity.Thm3.RSW.SeedComplementConnection
public import PottsContinuity.Thm3.RSW.EmbeddedFreeConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Cluster confinement and exterior-seed exploration

The localization step of Lemma 5 is graph-theoretic: an actual cluster contained
in W cannot meet any actual cluster seeded outside W. These statements have no
planarity or self-dual-parameter premise.
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedComplementGeometryVertexFintype : Fintype V := Fintype.ofFinite V
local instance seedComplementGeometryEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The empty-forbidden-set exploration is exactly actual connectivity from
one of the seeds. -/
theorem exteriorSeedCluster_mem_iff (S : Finset V) (A : Configuration G) (x : V) :
    x ∈ FKC.FiniteFK.wiredAvoidingClusterSet G ∅ S A ↔
      ∃ s ∈ S, ActualConnected G A s x := by
  constructor
  · rintro ⟨hx, s, hs, hconn⟩
    refine ⟨s.val, ?_, ?_⟩
    · simpa [FKC.FiniteFK.wiredAvoidingSeeds] using hs
    · exact embedded_restriction_actualConnected_mono
        (FKC.FiniteFK.wiredAvoidingVertexEmbedding ∅)
        (FKC.FiniteFK.wiredAvoidingGraph_map_le G ∅) A hconn
  · rintro ⟨s, hs, hconn⟩
    have hsC := FKC.FiniteFK.wiredAvoidingClusterSet_seed_subset
      (G := G) (∅ : Set V) S A (by simp) s hs
    change (openGraph G A).Reachable s x at hconn
    have hp := (SimpleGraph.reachable_iff_reflTransGen s x).mp hconn
    clear hconn
    induction hp with
    | refl => exact hsC
    | @tail z t hp hadj ih =>
      exact FKC.FiniteFK.wiredAvoidingClusterSet_openEdge_closed
        (∅ : Set V) S A ih (by simp) hadj

/-- The unexplored complement of all exterior-seed clusters lies inside W. -/
theorem exteriorSeedComplement_subset (W : Set V) (A : Configuration G) :
    FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A ⊆ W := by
  intro x hx
  by_contra hxW
  exact hx ((exteriorSeedCluster_mem_iff Wᶜ.toFinset A x).mpr
    ⟨x, by simpa using hxW, SimpleGraph.Reachable.refl x⟩)

/-- An actual cluster contained in W is disjoint from every cluster seeded
outside W, even when W meets the boundary of the ambient finite graph. -/
theorem confinedCluster_mem_exteriorSeedComplement (W : Set V) (A : Configuration G)
    (x : V) (hconfined : ∀ z, ActualConnected G A x z → z ∈ W) :
    x ∈ FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A := by
  intro hx
  obtain ⟨s, hs, hconn⟩ := (exteriorSeedCluster_mem_iff Wᶜ.toFinset A x).mp hx
  have hsW := hconfined s hconn.symm
  have hsnot : s ∉ W := by simpa using hs
  exact hsnot hsW

/-- Confinement puts both connected endpoints in the complement of the same
attained exterior-seed record. No representative or circuit is selected. -/
theorem confinedConnection_mem_exteriorSeedRecord (W : Set V)
    (A₀ A : Configuration G)
    (hrecord : A ∈ revealRecordEvent
      (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset) A₀)
    (x y : V) (hconn : ActualConnected G A x y)
    (hconfined : ∀ z, ActualConnected G A x z → z ∈ W) :
    x ∈ FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A₀ ∧
      y ∈ FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A₀ := by
  have hclusters := FKC.FiniteFK.wiredAvoidingClusterSet_eq_of_record
    (W := (∅ : Set V)) Wᶜ.toFinset A₀ A hrecord
  have hx := confinedCluster_mem_exteriorSeedComplement W A x hconfined
  have hy := confinedCluster_mem_exteriorSeedComplement W A y
    (fun z hz => hconfined z (hconn.trans hz))
  change x ∉ FKC.FiniteFK.wiredAvoidingClusterSet G ∅ Wᶜ.toFinset A₀ ∧
    y ∉ FKC.FiniteFK.wiredAvoidingClusterSet G ∅ Wᶜ.toFinset A₀
  rw [← hclusters]
  exact ⟨hx, hy⟩

end
end PottsContinuity.RSW
