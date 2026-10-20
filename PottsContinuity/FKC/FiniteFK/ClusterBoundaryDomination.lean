-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ClusterBoundaryDomination.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance clusterBoundaryEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance clusterBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
theorem componentSetoid_le_wired_union_of_edge_endpoints
    (ξ : BoundaryCondition V) (D : Set V) (A : Configuration G)
    (hA : ∀ ⦃e : G.edgeSet⦄, e ∈ A → ∀ ⦃u : V⦄, u ∈ e.1 → u ∈ D) :
    componentSetoid G ξ A ≤ (BoundaryCondition.wired (ξ.boundary ∪ D)).partition := by
  apply componentSetoid_le
  · apply reachableSetoid_le_of_adj (openGraph G A)
      (BoundaryCondition.wired (ξ.boundary ∪ D)).partition
    intro x y hxy
    rw [openGraph_adj] at hxy
    rcases hxy with ⟨e, heA, hexy⟩
    apply (BoundaryCondition.wired_rel (ξ.boundary ∪ D) x y).2
    right
    constructor
    · exact Set.mem_union_right _ (hA heA (by rw [hexy]; exact (Sym2.mem_iff').2 (Or.inl rfl)))
    · exact Set.mem_union_right _ (hA heA (by rw [hexy]; exact (Sym2.mem_iff').2 (Or.inr rfl)))
  · intro x y hxy
    apply (BoundaryCondition.wired_rel (ξ.boundary ∪ D) x y).2
    rcases ξ.supported hxy with rfl | ⟨hx, hy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.mem_union_left _ hx, Set.mem_union_left _ hy⟩

omit [Finite V] in
private theorem actualConnected_of_config_edge_endpoints
    (A : Configuration G) {e : G.edgeSet} (he : e ∈ A)
    {u v : V} (hu : u ∈ e.1) (hv : v ∈ e.1) :
    ActualConnected G A u v := by
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have hval : e.val = s(a,b) := by simpa using hab.symm
  have hE : s(a,b) ∈ G.edgeSet := by rw [← hval]; exact e.2
  have hAdj : G.Adj a b := G.mem_edgeSet.mp hE
  have hOpen : (openGraph G A).Adj a b := by
    rw [openGraph_adj]
    exact ⟨e, he, hab.symm⟩
  have hu' : u = a ∨ u = b := by
    rw [← hab] at hu
    exact (Sym2.mem_iff').mp hu
  have hv' : v = a ∨ v = b := by
    rw [← hab] at hv
    exact (Sym2.mem_iff').mp hv
  have habConn : ActualConnected G A a b := actualConnected_of_adj G A hOpen
  have hbaConn : ActualConnected G A b a := by
    change (openGraph G A).Reachable b a
    exact hOpen.reachable.symm
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact habConn
  · exact hbaConn
  · exact SimpleGraph.Reachable.refl _

theorem actualMultiClusterRecord_endpoint_connected
    (S : Finset V) (A₀ : Configuration G) {e : G.edgeSet}
    (he : e ∈ (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀).val)
    {u : V} (hu : u ∈ e.1) : actualMultiClusterConnected G S A₀ u := by
  have heA : e ∈ A₀ := (Finset.mem_inter.mp he).1
  have heReveal : e ∈ actualMultiClusterReveal G S A₀ := (Finset.mem_inter.mp he).2
  rcases (actualMultiClusterReveal_mem_iff S A₀ e).mp heReveal with
    ⟨v, hv, s, hs, hconn⟩
  refine ⟨s, hs, ?_⟩
  by_cases huv : u = v
  · simpa [huv] using hconn
  · have hconnUV : ActualConnected G A₀ u v :=
      actualConnected_of_config_edge_endpoints A₀ heA hu hv
    exact (show ActualConnected G A₀ s u from by
      change (openGraph G A₀).Reachable s u
      exact hconn.trans hconnUV.symm)

end
end PottsContinuity.FKC.FiniteFK
