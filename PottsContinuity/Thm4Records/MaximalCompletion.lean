module

public import PottsContinuity.Thm4Records.ExteriorFreeze

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

section Generic
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance completionEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
local instance completionEdgeFinite : Fintype G.edgeSet := Fintype.ofFinite _

end Generic

local instance clusterCompletionSourceEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- Each original censored side-cluster record is contained in the common reveal. -/
theorem sideOuterClusterReveal_subset_connectorReveal (m : ℕ) (hm : 1 ≤ m)
    (right : Bool) (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    sideOuterClusterReveal m right A ⊆ connectorReveal m hm A := by
  intro e he
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  cases right with
  | false => exact Finset.mem_union_left _ he
  | true => exact Finset.mem_union_right _ he

/-- The complete censored side cluster is unchanged on each common record. -/
theorem sideOuterCluster_eq_of_connector_record (m : ℕ) (hm : 1 ≤ m)
    (right : Bool) (A B : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (h : B ∈ revealRecordEvent (connectorReveal m hm) A) :
    Thm3.Prop4.censoredSeedCluster (sideCensoredGraph_le m right) (sideOuterSeeds m right) B =
    Thm3.Prop4.censoredSeedCluster (sideCensoredGraph_le m right) (sideOuterSeeds m right) A := by
  exact Thm3.Prop4.censoredSeedCluster_eq_of_agreement _ _ A B
    (recorded_agreement_of_subset A B _ _
      (sideOuterClusterReveal_subset_connectorReveal m hm right A) h.2)

end
end PottsContinuity.Thm4Records
