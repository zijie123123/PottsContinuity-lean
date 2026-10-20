module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace PottsContinuity.Push

/-- Every nontrivial component of a finite forest has two DISTINCT vertices
with unique neighbors in the ORIGINAL graph, not merely in an arbitrary
induced restriction. Component membership preserves all original neighbors. -/
theorem forest_component_has_two_original_leaves {V : Type*} [Finite V]
    (G : SimpleGraph V) (hforest : G.IsAcyclic) (u v : V) (huv : G.Adj u v) :
    ∃ a b : V, a ≠ b ∧ G.Reachable u a ∧ G.Reachable u b ∧
      (∃! w, G.Adj a w) ∧ (∃! w, G.Adj b w) := by
  classical
  let C := G.connectedComponentMk u
  have huC : u ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp huC huv
  let : Fintype C := Fintype.ofFinite _
  let : Nontrivial C := ⟨⟨⟨u,huC⟩,⟨v,hvC⟩,by
    intro heq
    exact huv.ne (congrArg Subtype.val heq)⟩⟩
  have htree : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,hforest.induce C.supp⟩
  obtain ⟨a,b,hab,ha,hb⟩ := htree.exists_ne_and_degree_eq_one
  have hleaf : ∀ c : C, C.toSimpleGraph.degree c=1 → ∃! w : V, G.Adj c.val w := by
    intro c hc
    obtain ⟨w,hw,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hc
    refine ⟨w.val,hw,?_⟩
    intro z hcz
    let z' : C := ⟨z,C.mem_supp_of_adj_mem_supp c.property hcz⟩
    exact congrArg Subtype.val (hunique z' hcz)
  exact ⟨a.val,b.val,(fun heq => hab (Subtype.ext heq)),
    C.reachable_of_mem_supp huC a.property,C.reachable_of_mem_supp huC b.property,
    hleaf a ha,hleaf b hb⟩

end PottsContinuity.Push
