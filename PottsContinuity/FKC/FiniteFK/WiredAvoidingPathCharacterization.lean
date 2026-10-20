-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingPathCharacterization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterExploration
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.CrossingComponentRemoval
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance avoidingPathGraphEdgeFintype (W : Set V) :
    Fintype (G.induce Wᶜ).edgeSet := Fintype.ofFinite _
local instance avoidingPathGraphEdgeDecidableEq (W : Set V) :
    DecidableEq (G.induce Wᶜ).edgeSet := Classical.decEq _
local instance avoidingPathOuterEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance avoidingPathOuterEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
/-- Restricting a configuration to the forbidden-set complement restricts the
actual open graph to the induced complement graph. -/
theorem wiredAvoiding_openGraph_eq_induce (W : Set V) (A : Configuration G) :
    openGraph (wiredAvoidingGraph G W) (wiredAvoidingConfiguration G W A) =
      (openGraph G A).induce Wᶜ := by
  let H := wiredAvoidingGraph G W
  let f := wiredAvoidingVertexEmbedding W
  let B := wiredAvoidingConfiguration G W A
  ext u v
  rw [openGraph_adj_iff_openBond]
  constructor
  · rintro ⟨hH, he⟩
    have hG : G.Adj u.val v.val := SimpleGraph.induce_adj.mp hH
    have hm := (mem_embeddedConfigurationRestriction
      H G f (wiredAvoidingGraph_map_le G W) A
      ⟨s(u, v), H.mem_edgeSet.mpr hH⟩).mp he
    have heq : embeddedEdgeEmbedding H G f (wiredAvoidingGraph_map_le G W)
        ⟨s(u, v), H.mem_edgeSet.mpr hH⟩ =
          ⟨s(u.val, v.val), G.mem_edgeSet.mpr hG⟩ := by
      apply Subtype.ext
      change f.sym2Map s(u, v) = _
      simp [f, wiredAvoidingVertexEmbedding]
    have hA : (⟨s(u.val, v.val), G.mem_edgeSet.mpr hG⟩ : G.edgeSet) ∈ A := heq ▸ hm
    exact SimpleGraph.induce_adj.mpr
      ((openGraph_adj_iff_openBond G A u.val v.val).mpr ⟨hG, hA⟩)
  · intro hOpen
    obtain ⟨hG, he⟩ := (openGraph_adj_iff_openBond G A u.val v.val).mp
      (SimpleGraph.induce_adj.mp hOpen)
    refine ⟨SimpleGraph.induce_adj.mpr hG, ?_⟩
    have heq : embeddedEdgeEmbedding H G f (wiredAvoidingGraph_map_le G W)
        ⟨s(u, v), H.mem_edgeSet.mpr (SimpleGraph.induce_adj.mpr hG)⟩ =
          ⟨s(u.val, v.val), G.mem_edgeSet.mpr hG⟩ := by
      apply Subtype.ext
      change f.sym2Map s(u, v) = _
      simp [f, wiredAvoidingVertexEmbedding]
    have hA : embeddedEdgeEmbedding H G f (wiredAvoidingGraph_map_le G W)
        ⟨s(u, v), H.mem_edgeSet.mpr (SimpleGraph.induce_adj.mpr hG)⟩ ∈ A :=
      heq.symm ▸ he
    exact (mem_embeddedConfigurationRestriction H G f (wiredAvoidingGraph_map_le G W)
      A ⟨s(u, v), H.mem_edgeSet.mpr (SimpleGraph.induce_adj.mpr hG)⟩).mpr hA

/-- Masked-cluster connectivity is exactly connectivity by an actual open walk
whose entire support avoids the forbidden set. -/
theorem wiredAvoidingClusterConnected_iff_walk_avoiding
    (W : Set V) (S : Finset V) (A : Configuration G) (x : V) :
    wiredAvoidingClusterConnected G W S A x ↔
      ∃ s ∈ S, ∃ p : (openGraph G A).Walk s x,
        ∀ v ∈ p.support, v ∉ W := by
  constructor
  · rintro ⟨hxW, s, hs, hconn⟩
    rcases (actualConnected_iff_walk _ _ _ _).mp hconn with ⟨p⟩
    rw [wiredAvoiding_openGraph_eq_induce] at p
    let p' := p.map (SimpleGraph.Embedding.induce Wᶜ).toHom
    refine ⟨s.val, ?_, ?_, ?_⟩
    · simpa [wiredAvoidingSeeds] using hs
    · simpa [p'] using p'
    · intro v hv
      change v ∈ (p.map (SimpleGraph.Embedding.induce Wᶜ).toHom).support at hv
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
      obtain ⟨u, hu, huv⟩ := hv
      subst v
      exact u.property
  · rintro ⟨s, hs, p, hp⟩
    have hsW : s ∉ W := by
      exact hp s p.start_mem_support
    have hxW : x ∉ W := hp x p.end_mem_support
    let p' := p.induce Wᶜ (fun v hv => hp v hv)
    rw [← wiredAvoiding_openGraph_eq_induce W A] at p'
    refine ⟨hxW, ⟨s, hsW⟩, ?_, (actualConnected_iff_walk _ _ _ _).mpr ⟨p'⟩⟩
    simp [wiredAvoidingSeeds, hs]

end
end PottsContinuity.FKC.FiniteFK
