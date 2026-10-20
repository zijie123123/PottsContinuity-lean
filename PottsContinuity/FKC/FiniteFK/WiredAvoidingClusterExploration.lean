-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingClusterExploration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.MultiSeedClusterExploration
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance avoidingVertexFintype (W : Set V) : Fintype {v : V // v ∉ W} :=
  Fintype.ofFinite _
local instance avoidingClusterEdgeFintype (W : Set V) :
    Fintype (G.induce Wᶜ).edgeSet := Fintype.ofFinite _
local instance avoidingClusterEdgeDecidableEq (W : Set V) :
    DecidableEq (G.induce Wᶜ).edgeSet := Classical.decEq _
local instance avoidingOuterEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance avoidingOuterEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The actual induced graph on vertices outside the forbidden wired set. -/
def wiredAvoidingGraph (G : SimpleGraph V) (W : Set V) : SimpleGraph {v : V // v ∉ W} :=
  G.induce Wᶜ

def wiredAvoidingVertexEmbedding (W : Set V) : {v : V // v ∉ W} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

omit [Finite V] in
theorem wiredAvoidingGraph_map_le (G : SimpleGraph V) (W : Set V) :
    (wiredAvoidingGraph G W).map (wiredAvoidingVertexEmbedding W) ≤ G := by
  intro u v huv
  rcases (SimpleGraph.map_adj (wiredAvoidingVertexEmbedding W)
      (wiredAvoidingGraph G W) u v).mp huv with ⟨u', v', hadj, rfl, rfl⟩
  exact SimpleGraph.induce_adj.mp hadj

def wiredAvoidingConfiguration (G : SimpleGraph V) (W : Set V)
    (A : Configuration G) : Configuration (wiredAvoidingGraph G W) :=
  embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
    (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) A

def wiredAvoidingSeeds (W : Set V) (S : Finset V) : Finset {v : V // v ∉ W} := by
  classical
  exact Finset.univ.filter (fun v : {v : V // v ∉ W} => v.val ∈ S)

/-- Actual open connectivity from a seed in `S` inside the induced graph on `Wᶜ`. -/
def wiredAvoidingClusterConnected (G : SimpleGraph V) (W : Set V) (S : Finset V)
    (A : Configuration G) (v : V) : Prop :=
  ∃ hv : v ∉ W,
    actualMultiClusterConnected (wiredAvoidingGraph G W) (wiredAvoidingSeeds W S)
      (wiredAvoidingConfiguration G W A) ⟨v, hv⟩

/-- Vertices reachable from `S` without entering `W`, using only actual open edges. -/
def wiredAvoidingClusterSet (G : SimpleGraph V) (W : Set V) (S : Finset V)
    (A : Configuration G) : Set V :=
  {v | wiredAvoidingClusterConnected G W S A v}

/-- Reveal every original edge incident to the masked cluster, including edges into `W`. -/
def wiredAvoidingClusterReveal (G : SimpleGraph V) (W : Set V) (S : Finset V)
    (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ wiredAvoidingClusterConnected G W S A u

theorem wiredAvoidingClusterSet_disjoint (W : Set V) (S : Finset V)
    (A : Configuration G) : Disjoint (wiredAvoidingClusterSet G W S A) W := by
  rw [Set.disjoint_left]
  intro v hvC hvW
  rcases hvC with ⟨hv, _⟩
  exact hv hvW

theorem wiredAvoidingClusterSet_seed_subset (W : Set V) (S : Finset V)
    (A : Configuration G) (hSW : ∀ s ∈ S, s ∉ W) :
    ∀ s ∈ S, s ∈ wiredAvoidingClusterSet G W S A := by
  intro s hs
  have hnot : s ∉ W := hSW s hs
  refine ⟨hnot, ?_⟩
  rw [actualMultiClusterConnected]
  refine ⟨⟨s, hnot⟩, ?_, ?_⟩
  · simp [wiredAvoidingSeeds, hs]
  · exact SimpleGraph.Reachable.refl _

theorem wiredAvoidingClusterSet_openEdge_closed (W : Set V) (S : Finset V)
    (A : Configuration G) {x y : V}
    (hx : x ∈ wiredAvoidingClusterSet G W S A)
    (hy : y ∉ W) (hxy : (openGraph G A).Adj x y) :
    y ∈ wiredAvoidingClusterSet G W S A := by
  classical
  rcases hx with ⟨hxW, hxconn⟩
  refine ⟨hy, ?_⟩
  rcases hxconn with ⟨s, hs, hconn⟩
  refine ⟨s, hs, ?_⟩
  apply hconn.trans
  have hadj : (wiredAvoidingGraph G W).Adj ⟨x, hxW⟩ ⟨y, hy⟩ := by
    change G.Adj x y
    exact (openGraph_le G A) hxy
  have hinnerOpen : (openGraph (wiredAvoidingGraph G W)
      (wiredAvoidingConfiguration G W A)).Adj ⟨x, hxW⟩ ⟨y, hy⟩ := by
    rw [openGraph_adj]
    rcases (openGraph_adj G A x y).mp hxy with ⟨e, he, heval⟩
    let ei : (wiredAvoidingGraph G W).edgeSet := ⟨s(⟨x, hxW⟩, ⟨y, hy⟩), hadj⟩
    have heq : embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
        (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei = e := by
      apply Subtype.ext
      change (wiredAvoidingVertexEmbedding W).sym2Map ei.1 = e.1
      simp [ei, Function.Embedding.sym2Map_apply, wiredAvoidingVertexEmbedding, heval]
    refine ⟨ei, ?_, ?_⟩
    · change ei ∈ embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
        (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) A
      rw [mem_embeddedConfigurationRestriction]
      rw [heq]
      exact he
    · rfl
  exact hinnerOpen.reachable

theorem wiredAvoidingClusterReveal_mem_iff (W : Set V) (S : Finset V)
    (A : Configuration G) (e : G.edgeSet) :
    e ∈ wiredAvoidingClusterReveal G W S A ↔
      ∃ u : V, u ∈ e.1 ∧ wiredAvoidingClusterConnected G W S A u := by
  classical
  simp [wiredAvoidingClusterReveal]

private theorem wiredAvoiding_innerReveal_agreement (W : Set V) (S : Finset V)
    (A B : Configuration G)
    (hagree : B ∩ wiredAvoidingClusterReveal G W S A =
      A ∩ wiredAvoidingClusterReveal G W S A) :
    wiredAvoidingConfiguration G W B ∩
        actualMultiClusterReveal (wiredAvoidingGraph G W) (wiredAvoidingSeeds W S)
          (wiredAvoidingConfiguration G W A) =
      wiredAvoidingConfiguration G W A ∩
        actualMultiClusterReveal (wiredAvoidingGraph G W) (wiredAvoidingSeeds W S)
          (wiredAvoidingConfiguration G W A) := by
  classical
  apply Finset.ext
  intro ei
  rw [Finset.mem_inter, Finset.mem_inter]
  have hstate := Finset.ext_iff.mp hagree
  constructor
  · rintro ⟨hB, hR⟩
    refine ⟨?_, hR⟩
    change ei ∈ embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) A
    rw [mem_embeddedConfigurationRestriction]
    have hOuter : embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
        (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈
        wiredAvoidingClusterReveal G W S A := by
      rcases (actualMultiClusterReveal_mem_iff (wiredAvoidingSeeds W S)
          (wiredAvoidingConfiguration G W A) ei).mp hR with ⟨u, hu, s, hs, hconn⟩
      rw [wiredAvoidingClusterReveal_mem_iff]
      refine ⟨u.val, ?_, ?_⟩
      · change (wiredAvoidingVertexEmbedding W) u ∈
          Sym2.map (wiredAvoidingVertexEmbedding W) ei.1
        exact Sym2.mem_map.mpr ⟨u, hu, rfl⟩
      · refine ⟨u.property, ?_⟩
        exact ⟨s, by simpa [wiredAvoidingSeeds] using hs, hconn⟩
    have h := hstate (embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei)
    have hiff : embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
        (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈ B ↔
        embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
          (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈ A := by
      simpa [Finset.mem_inter, hOuter] using h
    exact hiff.mp ((mem_embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) B ei).mp hB)
  · rintro ⟨hA, hR⟩
    refine ⟨?_, hR⟩
    change ei ∈ embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) B
    rw [mem_embeddedConfigurationRestriction]
    have hOuter : embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
        (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈
        wiredAvoidingClusterReveal G W S A := by
      rcases (actualMultiClusterReveal_mem_iff (wiredAvoidingSeeds W S)
          (wiredAvoidingConfiguration G W A) ei).mp hR with ⟨u, hu, s, hs, hconn⟩
      rw [wiredAvoidingClusterReveal_mem_iff]
      refine ⟨u.val, ?_, ?_⟩
      · change (wiredAvoidingVertexEmbedding W) u ∈
          Sym2.map (wiredAvoidingVertexEmbedding W) ei.1
        exact Sym2.mem_map.mpr ⟨u, hu, rfl⟩
      · refine ⟨u.property, ?_⟩
        exact ⟨s, by simpa [wiredAvoidingSeeds] using hs, hconn⟩
    have h := hstate (embeddedEdgeEmbedding (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei)
    have hiff : embeddedEdgeEmbedding (wiredAvoidingGraph G W)
        G (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈ A ↔
        embeddedEdgeEmbedding (wiredAvoidingGraph G W)
          G (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) ei ∈ B := by
      simpa [Finset.mem_inter, hOuter] using h.symm
    exact hiff.mp ((mem_embeddedConfigurationRestriction (wiredAvoidingGraph G W) G
      (wiredAvoidingVertexEmbedding W) (wiredAvoidingGraph_map_le G W) A ei).mp hA)

/-- Agreement on all recorded original edge states preserves the masked cluster. -/
theorem wiredAvoidingClusterSet_consistent (W : Set V) (S : Finset V)
    (A B : Configuration G)
    (hagree : B ∩ wiredAvoidingClusterReveal G W S A =
      A ∩ wiredAvoidingClusterReveal G W S A) :
    wiredAvoidingClusterSet G W S B = wiredAvoidingClusterSet G W S A := by
  classical
  apply Set.ext
  intro v
  change wiredAvoidingClusterConnected G W S B v ↔
    wiredAvoidingClusterConnected G W S A v
  by_cases hv : v ∈ W
  · simp [wiredAvoidingClusterConnected, hv]
  · have hconn := actualMultiClusterConnected_iff_of_reveal_agreement
      (G := wiredAvoidingGraph G W) (S := wiredAvoidingSeeds W S)
      (A := wiredAvoidingConfiguration G W A) (B := wiredAvoidingConfiguration G W B)
      (wiredAvoiding_innerReveal_agreement W S A B hagree) ⟨v, hv⟩
    change (∃ h : v ∉ W, actualMultiClusterConnected (wiredAvoidingGraph G W)
      (wiredAvoidingSeeds W S) (wiredAvoidingConfiguration G W B) ⟨v, h⟩) ↔
      (∃ h : v ∉ W, actualMultiClusterConnected (wiredAvoidingGraph G W)
        (wiredAvoidingSeeds W S) (wiredAvoidingConfiguration G W A) ⟨v, h⟩)
    constructor
    · rintro ⟨h', hc⟩
      have hp : h' = hv := Subsingleton.elim _ _
      subst h'
      exact ⟨hv, hconn.mp hc⟩
    · rintro ⟨h', hc⟩
      have hp : h' = hv := Subsingleton.elim _ _
      subst h'
      exact ⟨hv, hconn.mpr hc⟩

/-- The all-incident reveal is itself determined by its recorded states. -/
theorem wiredAvoidingClusterReveal_consistent (W : Set V) (S : Finset V)
    (A B : Configuration G)
    (hagree : B ∩ wiredAvoidingClusterReveal G W S A =
      A ∩ wiredAvoidingClusterReveal G W S A) :
    wiredAvoidingClusterReveal G W S B = wiredAvoidingClusterReveal G W S A := by
  classical
  ext e
  rw [wiredAvoidingClusterReveal_mem_iff, wiredAvoidingClusterReveal_mem_iff]
  have hC := wiredAvoidingClusterSet_consistent W S A B hagree
  have hconn (u : V) : wiredAvoidingClusterConnected G W S B u ↔
      wiredAvoidingClusterConnected G W S A u := by
    change u ∈ wiredAvoidingClusterSet G W S B ↔
      u ∈ wiredAvoidingClusterSet G W S A
    rw [hC]
  constructor
  · rintro ⟨u, hu, hc⟩
    exact ⟨u, hu, (hconn u).mp hc⟩
  · rintro ⟨u, hu, hc⟩
    exact ⟨u, hu, (hconn u).mpr hc⟩

end
end PottsContinuity.FKC.FiniteFK
