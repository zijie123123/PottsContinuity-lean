-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/MultiSeedClusterExploration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterComplementLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance multiSeedClusterEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance multiSeedClusterEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A vertex belongs to the union of the actual open clusters rooted at `S`. -/
def actualMultiClusterConnected (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) (u : V) : Prop :=
  ∃ s, s ∈ S ∧ ActualConnected G A s u

/-- All edges incident to any actual open cluster rooted at a seed in `S`. -/
def actualMultiClusterReveal (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u

theorem actualMultiClusterReveal_mem_iff (S : Finset V) (A : Configuration G)
    (e : G.edgeSet) :
    e ∈ actualMultiClusterReveal G S A ↔
      ∃ u : V, u ∈ e.1 ∧ ∃ s, s ∈ S ∧ ActualConnected G A s u := by
  classical
  change (e ∈ Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem actualClusterReveal_subset_multi (S : Finset V) (A : Configuration G)
    {s : V} (hs : s ∈ S) :
    actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := by
  intro e he
  rw [actualMultiClusterReveal_mem_iff]
  rcases (actualClusterReveal_mem_iff G s A e).mp he with ⟨u, hu, hconn⟩
  exact ⟨u, hu, s, hs, hconn⟩

private theorem single_reveal_agreement_of_multi
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    {s : V} (hs : s ∈ S) :
    B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
  classical
  apply Finset.ext
  intro e
  simp only [Finset.mem_inter]
  have heq := Finset.ext_iff.mp hagree e
  simp only [Finset.mem_inter] at heq
  constructor
  · rintro ⟨heB, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    exact ⟨(heq.mp ⟨heB, heMulti⟩).1, heSingle⟩
  · rintro ⟨heA, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    exact ⟨(heq.mpr ⟨heA, heMulti⟩).1, heSingle⟩

theorem actualMultiClusterConnected_iff_of_reveal_agreement
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    (u : V) :
    actualMultiClusterConnected G S B u ↔ actualMultiClusterConnected G S A u := by
  constructor
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mp hconn⟩
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mpr hconn⟩

theorem actualMultiClusterReveal_consistent
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A) :
    actualMultiClusterReveal G S B = actualMultiClusterReveal G S A := by
  ext e
  rw [actualMultiClusterReveal_mem_iff, actualMultiClusterReveal_mem_iff]
  constructor
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mp hconn⟩
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mpr hconn⟩

def actualMultiClusterComplementSet (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Set V :=
  {u | ¬ actualMultiClusterConnected G S A u}

def actualMultiClusterComplementEmbedding (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : actualMultiClusterComplementSet G S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgeRestriction_actualMultiClusterReveal_eq_induced_complement
    (S : Finset V) (A : Configuration G) :
    edgeRestriction G (actualMultiClusterReveal G S A) =
      (G.induce (actualMultiClusterComplementSet G S A)).map
        (actualMultiClusterComplementEmbedding G S A) := by
  ext x y
  constructor
  · intro hxy
    have hxy' : G.Adj x y ∧ s(x,y) ∉ openEdges G (actualMultiClusterReveal G S A) := by
      simpa [edgeRestriction] using hxy
    rcases hxy' with ⟨hAdj, hNot⟩
    have hnotConn :
        ¬ actualMultiClusterConnected G S A x ∧
        ¬ actualMultiClusterConnected G S A y := by
      constructor
      · intro hx
        apply hNot
        rcases hx with ⟨s, hs, hconn⟩
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualMultiClusterReveal G S A := by
          rw [actualMultiClusterReveal_mem_iff]
          exact ⟨x, (Sym2.mem_iff').2 (Or.inl rfl), s, hs, hconn⟩
        have hOpen := (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        simpa using hOpen
      · intro hy
        apply hNot
        rcases hy with ⟨s, hs, hconn⟩
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualMultiClusterReveal G S A := by
          rw [actualMultiClusterReveal_mem_iff]
          exact ⟨y, (Sym2.mem_iff').2 (Or.inr rfl), s, hs, hconn⟩
        have hOpen := (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        simpa using hOpen
    apply (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).2
    refine ⟨⟨x, hnotConn.1⟩, ⟨y, hnotConn.2⟩, ?_, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mpr hAdj
  · intro hxy
    rcases (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).1 hxy with
      ⟨u, w, hAdjInduced, hux, hwy⟩
    have hAdj : G.Adj u.val w.val := SimpleGraph.induce_adj.mp hAdjInduced
    have hux' : u.val = x := hux
    have hwy' : w.val = y := hwy
    subst x
    subst y
    rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro hmem
    have hR : (⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
        actualMultiClusterReveal G S A := by
      apply (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
        ⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩).mp
      simpa [actualMultiClusterComplementEmbedding] using hmem
    rcases (actualMultiClusterReveal_mem_iff S A _).mp hR with
      ⟨z, hz, s, hs, hconn⟩
    rcases (Sym2.mem_iff').mp hz with hzu | hzw
    · exact u.2 ⟨s, hs, hzu ▸ hconn⟩
    · exact w.2 ⟨s, hs, hzw ▸ hconn⟩

theorem actualMultiClusterComplementGraph_le
    (S : Finset V) (A : Configuration G) :
    (G.induce (actualMultiClusterComplementSet G S A)).map
      (actualMultiClusterComplementEmbedding G S A) ≤ G := by
  rw [← edgeRestriction_actualMultiClusterReveal_eq_induced_complement]
  exact edgeRestriction_le G (actualMultiClusterReveal G S A)

theorem actualMultiClusterReveal_eq_subgraphRemovedEdges
    (S : Finset V) (A : Configuration G) :
    actualMultiClusterReveal G S A =
      subgraphRemovedEdges
        ((G.induce (actualMultiClusterComplementSet G S A)).map
          (actualMultiClusterComplementEmbedding G S A)) G := by
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges]
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_actualMultiClusterReveal_eq_induced_complement (G := G) S A)
  rw [edgeRestriction_edgeSet] at hgraph
  rw [← hgraph]
  simp only [Set.mem_sdiff]
  simp [e.property, coe_mem_openEdges_iff]

end
end PottsContinuity.FKC.FiniteFK
