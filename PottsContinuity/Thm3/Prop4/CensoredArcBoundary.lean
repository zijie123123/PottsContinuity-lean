module

public import PottsContinuity.Thm3.Prop4.CensoredArcGeometry
public import PottsContinuity.Thm3.Prop4.ExteriorPartition
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# Boundary control after an arc-censored outside-cluster exploration

All recorded open edges have endpoints in the removed clusters or the prescribed
arc. Consequently the surviving induced domain has a boundary partition no larger
than wiring that arc. This is genuine boundary control, without a dual selector.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance censoredArcBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Seeds outside the arc have censored clusters disjoint from it. -/
theorem censoredArc_cluster_disjoint (W S : Set V) (hS : Disjoint S W)
    (A : Configuration G) {v : V}
    (hv : v ∈ censoredSeedCluster (arcCensoredGraph_le G W) S A) : v ∉ W := by
  obtain ⟨s,hs,hsv⟩ := hv
  exact arcCensored_connected_not_mem G W A
    (fun hsW => (Set.disjoint_left.mp hS) hs hsW) hsv

/-- An open ambient edge leaving a censored cluster must land on the prescribed arc. -/
theorem censoredArc_open_edge_endpoint (W S : Set V) (hS : Disjoint S W)
    (A : Configuration G) {e : G.edgeSet} (heA : e ∈ A)
    {x y : V} (hx : x ∈ e.val) (hy : y ∈ e.val)
    (hxc : x ∈ censoredSeedCluster (arcCensoredGraph_le G W) S A) :
    y ∈ censoredSeedCluster (arcCensoredGraph_le G W) S A ∪ W := by
  by_cases hyW : y ∈ W
  · exact Or.inr hyW
  apply Or.inl
  have hxW := censoredArc_cluster_disjoint W S hS A hxc
  by_cases hxy : x = y
  · exact hxy ▸ hxc
  have hopen : (openGraph G A).Adj x y := by
    obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e.val
    have habOpen : (openGraph G A).Adj a b :=
      (openGraph_adj G A a b).mpr ⟨e,heA,hab.symm⟩
    have hx' : x = a ∨ x = b := by rw [← hab] at hx; exact Sym2.mem_iff'.mp hx
    have hy' : y = a ∨ y = b := by rw [← hab] at hy; exact Sym2.mem_iff'.mp hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact False.elim (hxy rfl)
    · exact habOpen
    · exact habOpen.symm
    · exact False.elim (hxy rfl)
  have hstep := (censored_openGraph_adj_iff (arcCensoredGraph_le G W) A x y).mpr
    ⟨hopen,openGraph_le G A hopen,hxW,hyW⟩
  obtain ⟨s,hs,hsx⟩ := hxc
  exact ⟨s,hs,hsx.trans hstep.reachable⟩

/-- Every recorded open edge is wholly in the removed clusters together with the arc. -/
theorem censoredArc_record_open_endpoints (W S : Set V) (hS : Disjoint S W)
    (A : Configuration G) {e : G.edgeSet}
    (he : e ∈ (Exploration.revealRecordConfiguration
      (censoredSeedReveal (arcCensoredGraph_le G W) S) A).val)
    {y : V} (hy : y ∈ e.val) :
    y ∈ censoredSeedCluster (arcCensoredGraph_le G W) S A ∪ W := by
  have heA := (Finset.mem_inter.mp he).1
  obtain ⟨x,hxe,hxc⟩ := (mem_censoredSeedReveal _ S A e).mp (Finset.mem_inter.mp he).2
  exact censoredArc_open_edge_endpoint W S hS A heA hxe hy hxc

/-- Every seed belongs to the actual censored cluster union. -/
theorem subset_censoredSeedCluster {H : SimpleGraph V} (hHG : H ≤ G) (S : Set V) (A : Configuration G) :
    S ⊆ censoredSeedCluster hHG S A := by
  intro s hs
  exact ⟨s,hs,SimpleGraph.Reachable.refl _⟩

/-- The surviving carrier is a literal subset of the target domain when all exterior vertices
are seeds. No support outside that target is hidden in this restriction. -/
theorem censoredArc_complement_subset_domain (W D : Set V) (A : Configuration G) :
    (censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A)ᶜ ⊆ D := by
  intro x hx
  by_contra hxD
  exact hx (subset_censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A hxD)

/-- Exact induced-partition domination by the target arc after the actual stopped exploration.
The ambient boundary may be arbitrary outside the target domain. -/
theorem censoredArc_frozen_partition_le_wired (W D : Set V) (hWD : W ⊆ D)
    (ξ : BoundaryCondition V) (hξ : ξ.boundary ⊆ Dᶜ ∪ W) (A : Configuration G) :
    let C := censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A
    let f : (Cᶜ : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ
      (Exploration.revealRecordConfiguration
        (censoredSeedReveal (arcCensoredGraph_le G W) Dᶜ) A).val)).partition ≤
      (BoundaryCondition.wired (f ⁻¹' W)).partition := by
  dsimp only
  intro a b hab
  have hSW : Disjoint Dᶜ W := Set.disjoint_left.mpr (fun _ hD hW => hD (hWD hW))
  have hlarge := componentSetoid_le_wired_union_of_edge_endpoints ξ
    (censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A ∪ W)
    (Exploration.revealRecordConfiguration
      (censoredSeedReveal (arcCensoredGraph_le G W) Dᶜ) A).val
    (fun _ he _ hy => censoredArc_record_open_endpoints W Dᶜ hSW A he hy) hab
  have haW : ∀ z : ((censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A)ᶜ : Set V),
      z.val ∈ ξ.boundary ∪ (censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A ∪ W) →
        z.val ∈ W := by
    intro z hz
    rcases hz with hz | hz
    · rcases hξ hz with hz | hz
      · exact False.elim (z.property (subset_censoredSeedCluster _ Dᶜ A hz))
      · exact hz
    · rcases hz with hz | hz
      · exact False.elim (z.property hz)
      · exact hz
  rcases (BoundaryCondition.wired_rel _ a.val b.val).mp hlarge with heq | ⟨ha,hb⟩
  · exact (BoundaryCondition.wired_rel _ a b).mpr (Or.inl (Subtype.ext heq))
  · exact (BoundaryCondition.wired_rel _ a b).mpr (Or.inr ⟨haW a ha,haW b hb⟩)

end
end PottsContinuity.Thm3.Prop4
