module

public import PottsContinuity.Thm3.Push.ClosedClusterReveal
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
local instance frontierEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance frontierAuxEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- The vertices reached from the specified auxiliary seeds along edges
whose corresponding original primal bonds are closed. -/
def closedClusterReached (e : G.edgeSet ≃ H.edgeSet) (S : Finset W)
    (A : Configuration G) : Set W :=
  {v | ∃ s ∈ S, ActualConnected H (auxiliaryClosedConfiguration e A) s v}

theorem mem_closedClusterReveal_iff_endpoint (e : G.edgeSet ≃ H.edgeSet)
    (S : Finset W) (A : Configuration G) (f : G.edgeSet) :
    f ∈ closedClusterReveal e S A ↔
      ∃ v ∈ (e f).val, v ∈ closedClusterReached e S A := by
  rw [mem_closedClusterReveal]
  exact FKC.FiniteFK.actualMultiClusterReveal_mem_iff S _ (e f)

theorem closedClusterReached_eq_of_reveal_agreement (e : G.edgeSet ≃ H.edgeSet)
    (S : Finset W) (A B : Configuration G)
    (hagree : B ∩ closedClusterReveal e S A = A ∩ closedClusterReveal e S A) :
    closedClusterReached e S B = closedClusterReached e S A := by
  ext v
  exact closedCluster_reached_iff_of_reveal_agreement e S A B hagree v

omit [Finite W] in
/-- A dual edge leaving the explored closed cluster crosses an OPEN original
bond. This proves the sampled-edge state of the whole primal frontier. -/
theorem closedCluster_frontier_primal_open (e : G.edgeSet ≃ H.edgeSet)
    (S : Finset W) (A : Configuration G) {u v : W} (huv : H.Adj u v)
    (hu : u ∈ closedClusterReached e S A) (hv : v ∉ closedClusterReached e S A) :
    e.symm ⟨s(u,v), H.mem_edgeSet.mpr huv⟩ ∈ A := by
  classical
  by_contra hnot
  let f : H.edgeSet := ⟨s(u,v), H.mem_edgeSet.mpr huv⟩
  have hf : f ∈ auxiliaryClosedConfiguration e A :=
    (mem_auxiliaryClosedConfiguration e A f).mpr hnot
  have hadj : (openGraph H (auxiliaryClosedConfiguration e A)).Adj u v := by
    rw [openGraph_adj]
    exact ⟨f, hf, rfl⟩
  obtain ⟨s, hs, hsu⟩ := hu
  exact hv ⟨s, hs, hsu.trans hadj.reachable⟩

end
end PottsContinuity.Push
