module

public import PottsContinuity.Thm3.Prop4.CensoredArcBoundary
public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# First-hit connections surviving the censored outside-cluster exploration

A connection may visit removed clusters after touching the target arc. We retain
only its prefix up to an arc hit. Thus the surviving witness is proved rather
than assuming that its entire original path avoids the removed vertices.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance censoredConnectionEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A root outside the censored clusters retains an actual connection to the arc
when all edges incident to those clusters are erased. -/
theorem censoredArc_target_survives_erasure (W S : Set V) (hSW : Disjoint S W)
    (A : Configuration G) (x : V)
    (hx : x ∉ censoredSeedCluster (arcCensoredGraph_le G W) S A)
    (hconn : A ∈ targetConnectionEvent x W) :
    RSW.inducedConfigurationErasure
      (censoredSeedCluster (arcCensoredGraph_le G W) S A)ᶜ A ∈
        targetConnectionEvent x W := by
  let C := censoredSeedCluster (arcCensoredGraph_le G W) S A
  have hwalk : ∀ {u v : V} (p : (openGraph G A).Walk u v), v ∈ W → u ∉ C →
      ∃ z ∈ W, ActualConnected G (RSW.inducedConfigurationErasure Cᶜ A) u z := by
    intro u v p
    induction p with
    | nil =>
      intro hu _
      exact ⟨_,hu,SimpleGraph.Reachable.refl _⟩
    | @cons u v w huv p ih =>
      intro hw hu
      by_cases huW : u ∈ W
      · exact ⟨u,huW,SimpleGraph.Reachable.refl _⟩
      have hv : v ∉ C := by
        intro hvC
        obtain ⟨e,he,heq⟩ := (openGraph_adj G A u v).mp huv
        have hvE : v ∈ e.val := by rw [heq]; exact Sym2.mem_iff'.mpr (Or.inr rfl)
        have huE : u ∈ e.val := by rw [heq]; exact Sym2.mem_iff'.mpr (Or.inl rfl)
        rcases censoredArc_open_edge_endpoint W S hSW A he hvE huE hvC with huC | huW'
        · exact hu huC
        · exact huW huW'
      obtain ⟨z,hz,hvz⟩ := ih hw hv
      have hedge : (openGraph G (RSW.inducedConfigurationErasure Cᶜ A)).Adj u v := by
        obtain ⟨e,he,heq⟩ := (openGraph_adj G A u v).mp huv
        apply (openGraph_adj G _ u v).mpr
        refine ⟨e,(RSW.mem_inducedConfigurationErasure Cᶜ A e).mpr ⟨he,?_⟩,heq⟩
        intro y hy
        rw [heq] at hy
        rcases Sym2.mem_iff'.mp hy with hy | hy
        · rw [hy]
          exact hu
        · rw [hy]
          exact hv
      exact ⟨z,hz,hedge.reachable.trans hvz⟩
  obtain ⟨y,hy,⟨p⟩⟩ := hconn
  exact hwalk p hy hx

/-- The same retained first-hit witness is valid on every state of an attained record. -/
theorem censoredArc_target_survives_record (W S : Set V) (hSW : Disjoint S W)
    (A₀ A : Configuration G) (x : V)
    (hrecord : A ∈ Exploration.revealRecordEvent
      (censoredSeedReveal (arcCensoredGraph_le G W) S) A₀)
    (hx : x ∉ censoredSeedCluster (arcCensoredGraph_le G W) S A₀)
    (hconn : A ∈ targetConnectionEvent x W) :
    RSW.inducedConfigurationErasure
      (censoredSeedCluster (arcCensoredGraph_le G W) S A₀)ᶜ A ∈
        targetConnectionEvent x W := by
  have hC := censoredSeedCluster_eq_of_agreement (arcCensoredGraph_le G W) S A₀ A hrecord.2
  rw [← hC]
  exact censoredArc_target_survives_erasure W S hSW A x (by rw [hC]; exact hx) hconn

end
end PottsContinuity.Thm3.Prop4
