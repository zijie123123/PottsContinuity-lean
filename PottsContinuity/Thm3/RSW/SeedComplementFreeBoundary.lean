module

public import PottsContinuity.Thm3.RSW.MultiSeedComplementLaw
public import PottsContinuity.Exploration.FrozenBoundaryFreeInterior
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Freeness after exploring every cluster from the original boundary -/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance seedComplementFreeBoundaryEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance seedComplementFreeBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- An unexplored vertex has no incident recorded open edge. Revealed closed
edges are retained in the record and create no boundary connection. -/
theorem seedComplement_no_recorded_open_neighbor (S : Finset V) (A : Configuration G)
    (u : V) (hu : u ∈ FKC.FiniteFK.actualMultiClusterComplementSet G S A) :
    ∀ v, ¬ (openGraph G
      (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A).val).Adj u v := by
  intro v hadj
  obtain ⟨e,he,hev⟩ := (openGraph_adj G _ u v).mp hadj
  change e ∈ A ∩ FKC.FiniteFK.actualMultiClusterReveal G S A at he
  obtain ⟨heA,heR⟩ := Finset.mem_inter.mp he
  obtain ⟨w,hw,s,hs,hconn⟩ :=
    (FKC.FiniteFK.actualMultiClusterReveal_mem_iff S A e).mp heR
  have huv : (openGraph G A).Adj u v := (openGraph_adj G A u v).mpr ⟨e,heA,hev⟩
  change ¬ FKC.FiniteFK.actualMultiClusterConnected G S A u at hu
  rw [hev] at hw
  rcases (Sym2.mem_iff').mp hw with rfl | rfl
  · exact hu ⟨s,hs,hconn⟩
  · exact hu ⟨s,hs,hconn.trans huv.symm.reachable⟩

/-- If every original boundary vertex is a seed, then the exact frozen
partition on the whole unexplored complement is discrete. -/
theorem seedComplement_frozen_partition_free
    (ξ : BoundaryCondition V) (S : Finset V) (A : Configuration G)
    (hseeds : ∀ u ∈ ξ.boundary, u ∈ S)
    {u v : V}
    (hu : u ∈ FKC.FiniteFK.actualMultiClusterComplementSet G S A)
    (hv : v ∈ FKC.FiniteFK.actualMultiClusterComplementSet G S A) :
    (frozenBoundary ξ
      (Exploration.revealRecordConfiguration (FKC.FiniteFK.actualMultiClusterReveal G S) A).val).partition.r u v ↔
      u = v := by
  apply Exploration.frozenBoundary_partition_free_on_isolated ξ _
    (FKC.FiniteFK.actualMultiClusterComplementSet G S A) _
    (seedComplement_no_recorded_open_neighbor S A) hu hv
  apply Set.disjoint_left.mpr
  intro z hz hb
  exact hz ⟨z,hseeds z hb,SimpleGraph.Reachable.refl z⟩

end
end PottsContinuity.RSW
