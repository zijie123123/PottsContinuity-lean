-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingClusterComplement.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterExploration
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The vertices not reached by the actual masked cluster. -/
def wiredAvoidingComplementSet (G : SimpleGraph V) (W : Set V) (S : Finset V)
    (A : Configuration G) : Set V := (wiredAvoidingClusterSet G W S A)ᶜ

def wiredAvoidingComplementEmbedding (G : SimpleGraph V) (W : Set V) (S : Finset V)
    (A : Configuration G) : wiredAvoidingComplementSet G W S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

local instance wiredAvoidingComplementGraphEdgeFintype (W : Set V) (S : Finset V)
    (A : Configuration G) : Fintype
      ((G.induce (wiredAvoidingClusterSet G W S A)ᶜ).map
        (wiredAvoidingComplementEmbedding G W S A)).edgeSet := Fintype.ofFinite _
local instance wiredAvoidingComplementGraphEdgeDecidableEq (W : Set V) (S : Finset V)
    (A : Configuration G) : DecidableEq
      ((G.induce (wiredAvoidingClusterSet G W S A)ᶜ).map
        (wiredAvoidingComplementEmbedding G W S A)).edgeSet := Classical.decEq _

theorem wiredAvoidingComplementGraph_le (W : Set V) (S : Finset V)
    (A : Configuration G) :
    ((G.induce (wiredAvoidingComplementSet G W S A)).map
      (wiredAvoidingComplementEmbedding G W S A)) ≤ G := by
  intro u v huv
  rcases (SimpleGraph.map_adj (wiredAvoidingComplementEmbedding G W S A)
    (G.induce (wiredAvoidingComplementSet G W S A)) u v).mp huv with
    ⟨u', v', hadj, rfl, rfl⟩
  exact SimpleGraph.induce_adj.mp hadj

theorem edgeRestriction_wiredAvoidingClusterReveal_eq_complement
    (W : Set V) (S : Finset V) (A : Configuration G) :
    edgeRestriction G (wiredAvoidingClusterReveal G W S A) =
      (G.induce (wiredAvoidingComplementSet G W S A)).map
        (wiredAvoidingComplementEmbedding G W S A) := by
  classical
  ext x y
  constructor
  · intro hxy
    have hxy' : G.Adj x y ∧ s(x,y) ∉ openEdges G (wiredAvoidingClusterReveal G W S A) := by
      simpa [edgeRestriction] using hxy
    rcases hxy' with ⟨hAdj, hNot⟩
    have hx : x ∉ wiredAvoidingClusterSet G W S A := by
      intro hx
      apply hNot
      have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
          wiredAvoidingClusterReveal G W S A := by
        rw [wiredAvoidingClusterReveal_mem_iff]
        exact ⟨x, (Sym2.mem_iff').2 (Or.inl rfl), hx⟩
      exact (coe_mem_openEdges_iff G (wiredAvoidingClusterReveal G W S A)
        ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
    have hy : y ∉ wiredAvoidingClusterSet G W S A := by
      intro hy
      apply hNot
      have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
          wiredAvoidingClusterReveal G W S A := by
        rw [wiredAvoidingClusterReveal_mem_iff]
        exact ⟨y, (Sym2.mem_iff').2 (Or.inr rfl), hy⟩
      exact (coe_mem_openEdges_iff G (wiredAvoidingClusterReveal G W S A)
        ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
    apply (SimpleGraph.map_adj (wiredAvoidingComplementEmbedding G W S A)
      (G.induce (wiredAvoidingComplementSet G W S A)) x y).2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mpr hAdj
  · intro hxy
    rcases (SimpleGraph.map_adj (wiredAvoidingComplementEmbedding G W S A)
      (G.induce (wiredAvoidingComplementSet G W S A)) x y).1 hxy with
      ⟨u, v, hadj, hux, hvy⟩
    have hAdj : G.Adj u.val v.val := SimpleGraph.induce_adj.mp hadj
    have hu : u.val ∉ wiredAvoidingClusterSet G W S A := u.property
    have hv : v.val ∉ wiredAvoidingClusterSet G W S A := v.property
    have hux' : u.val = x := hux
    have hvy' : v.val = y := hvy
    subst x
    subst y
    rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro hmem
    have hR : (⟨s(u.val,v.val), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
        wiredAvoidingClusterReveal G W S A := by
      apply (coe_mem_openEdges_iff G (wiredAvoidingClusterReveal G W S A)
        ⟨s(u.val,v.val), G.mem_edgeSet.mpr hAdj⟩).mp
      simpa [wiredAvoidingComplementEmbedding] using hmem
    rcases (wiredAvoidingClusterReveal_mem_iff W S A _).mp hR with ⟨z, hz, hzC⟩
    rcases (Sym2.mem_iff').mp hz with hzu | hzv
    · exact hu (hzu ▸ hzC)
    · exact hv (hzv ▸ hzC)

theorem wiredAvoidingClusterReveal_eq_subgraphRemovedEdges
    (W : Set V) (S : Finset V) (A : Configuration G) :
    wiredAvoidingClusterReveal G W S A =
      subgraphRemovedEdges
        ((G.induce (wiredAvoidingComplementSet G W S A)).map
          (wiredAvoidingComplementEmbedding G W S A)) G := by
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges]
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_wiredAvoidingClusterReveal_eq_complement (G := G) W S A)
  rw [edgeRestriction_edgeSet] at hgraph
  rw [← hgraph]
  simp only [Set.mem_sdiff]
  simp [e.property, coe_mem_openEdges_iff]

/-- Conditioning on the full actual masked-cluster record leaves the exact
FK law on the induced complement, with the original exterior wiring and all
recorded boundary connections pulled back. -/
theorem law_filter_wiredAvoidingClusterRecord_map_complement
    (q : ClusterWeight) (ξ : BoundaryCondition V) (W : Set V) (S : Finset V)
    (A₀ : Configuration G) :
    ((law G q ξ).filter
      (revealRecordEvent G (wiredAvoidingClusterReveal G W S) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G (wiredAvoidingClusterReveal G W S)
          (fun C C' hagree => wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
        exact frozenStateEvent_support q ξ (wiredAvoidingClusterReveal G W S A₀)
          (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀))).map
        (embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G W S A₀)) G
          (wiredAvoidingComplementEmbedding G W S A₀)
          (wiredAvoidingComplementGraph_le (G := G) W S A₀)) =
      law (G.induce (wiredAvoidingComplementSet G W S A₀)) q
        (isolatedExtensionPullbackBoundary (wiredAvoidingComplementEmbedding G W S A₀)
          (frozenBoundary ξ
            (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val)) := by
  let C := wiredAvoidingComplementSet G W S A₀
  let f := wiredAvoidingComplementEmbedding G W S A₀
  let H := (G.induce C).map f
  let R := wiredAvoidingClusterReveal G W S A₀
  let K := revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀
  have hR : R = subgraphRemovedEdges H G := by
    simpa [R, H, C, f, wiredAvoidingComplementSet] using wiredAvoidingClusterReveal_eq_subgraphRemovedEdges (G := G) W S A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    rw [← hR]
    exact K.property
  have hHG : H ≤ G := wiredAvoidingComplementGraph_le (G := G) W S A₀
  have hconditional := law_filter_frozen_map_embeddedRestriction
    (G.induce C) G f hHG q ξ K'
  have hevent : revealRecordEvent G (wiredAvoidingClusterReveal G W S) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [revealRecordEvent_eq_frozenStateEvent G (wiredAvoidingClusterReveal G W S)
      (fun C C' hagree => wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
    ext C'
    simp [frozenStateEvent, K', K, R, hR]
  have hfiltered :
      (law G q ξ).filter (revealRecordEvent G (wiredAvoidingClusterReveal G W S) A₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent G (wiredAvoidingClusterReveal G W S)
            (fun C C' hagree => wiredAvoidingClusterReveal_consistent W S C C' hagree) A₀]
          exact frozenStateEvent_support q ξ (wiredAvoidingClusterReveal G W S A₀)
            (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀)) =
      (law G q ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    ext C'
    rw [PMF.filter_apply, PMF.filter_apply, hevent]
  have hfilter := congrArg
    (fun P : PMF (Configuration G) =>
      PMF.map (embeddedConfigurationRestriction (G.induce C) G f hHG) P) hfiltered
  simpa [H, f, K, R, C, K', wiredAvoidingComplementSet, isolatedExtensionPullbackBoundary, hR] using
    hfilter.trans hconditional

end
end PottsContinuity.FKC.FiniteFK
