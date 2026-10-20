module

public import PottsContinuity.Thm4Records.MaximalCompletion

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

section Generic
variable {V : Type*} [Finite V] {G H : SimpleGraph V}
local instance frontierSourceEq : DecidableEq G.edgeSet := Classical.decEq _
local instance frontierCensoredEq : DecidableEq H.edgeSet := Classical.decEq _

/-- An actual open censored bond cannot leave the explored seed cluster. -/
theorem censoredSeedCluster_closed_under_open_adj
    (hHG : H ≤ G) (S : Set V) (A : Configuration G) {u v : V}
    (hu : u ∈ Thm3.Prop4.censoredSeedCluster hHG S A)
    (huv : (openGraph H (Thm3.Prop4.censoredConfiguration hHG A)).Adj u v) :
    v ∈ Thm3.Prop4.censoredSeedCluster hHG S A := by
  obtain ⟨s,hs,hsu⟩ := hu
  exact ⟨s,hs,hsu.trans huv.reachable⟩

end Generic

local instance sourceFrontierEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- A vertex on the opposite side reached by a side seed is decided by the
concrete common record, including when the connection fails. -/
theorem sideSeedConnection_readFrom_connectorReveal (m : ℕ) (hm : 1 ≤ m)
    (right : Bool) (S : Set (FKC.FiniteFK.SlitBoxVertex (16*m))) :
    ReadFromReveal (connectorReveal m hm)
      {A | ∃ v ∈ S, v ∈ Thm3.Prop4.censoredSeedCluster
        (sideCensoredGraph_le m right) (sideOuterSeeds m right) A} := by
  intro A B hB
  simp only [Set.mem_ofPred_eq]
  rw [sideOuterCluster_eq_of_connector_record m hm right A B hB]

end
end PottsContinuity.Thm4Records
