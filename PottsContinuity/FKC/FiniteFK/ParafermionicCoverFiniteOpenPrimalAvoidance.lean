-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverFiniteOpenPrimalAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverSameSheetBridge
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConfigurationExtension
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedOpenPrimalAvoidance
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
open PottsContinuity.FKC.Medial
open SimpleGraph

/-- Every dart of the actual inclusion image of a finite open walk has true
state in the genuine finite-box configuration extension. -/
theorem parafermionicCoverBoxOpenWalkHom_dart_state_true
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v) :
    ∀ d ∈ (w.map (parafermionicCoverBoxOpenWalkHom n A)).darts,
      parafermionicCoverConfigurationExtensionState n A ⟨d.edge, d.edge_mem⟩ = true := by
  intro d hd
  rw [Walk.darts_map] at hd
  rcases List.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
  have hopen : d₀.edge ∈ openEdges (ParafermionicAmbientGraph n) A := by
    rw [← openGraph_edgeSet]
    exact d₀.edge_mem
  obtain ⟨e₀, he₀, heval⟩ := hopen
  have htarget :
      (embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
        (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n) e₀).val =
        ((parafermionicCoverBoxOpenWalkHom n A).mapDart d₀).edge := by
    change Sym2.map (parafermionicCoverBoxVertexEmbedding n) e₀.val =
      Sym2.map (parafermionicCoverBoxVertexEmbedding n) d₀.edge
    rw [heval]
  have hmem :
      (embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
        (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n) e₀) ∈
          parafermionicCoverConfigurationExtension n A := by
    rw [parafermionicCoverConfigurationExtension_inside]
    exact he₀
  have htarget' :
      embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
        (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n) e₀ =
      (⟨((parafermionicCoverBoxOpenWalkHom n A).mapDart d₀).edge,
        ((parafermionicCoverBoxOpenWalkHom n A).mapDart d₀).edge_mem⟩ :
        parafermionicCoverGraph.edgeSet) := by
    apply Subtype.ext
    exact htarget
  have htargetMem :
      (⟨((parafermionicCoverBoxOpenWalkHom n A).mapDart d₀).edge,
        ((parafermionicCoverBoxOpenWalkHom n A).mapDart d₀).edge_mem⟩ :
        parafermionicCoverGraph.edgeSet) ∈ parafermionicCoverConfigurationExtension n A := by
    rw [← htarget']
    exact hmem
  exact (parafermionicCoverConfigurationExtensionState_eq_true_iff n A _).2 htargetMem

/-- A finite open walk, included literally in the full cover graph and refined
at every coarse center, avoids every actual refined pairing walk. -/
theorem parafermionicCoverBoxOpenWalk_refinement_avoidsPairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicAmbientVertex n}
    (w : (openGraph (ParafermionicAmbientGraph n) A).Walk u v)
    {a b : ParafermionicCoverFinitePort n × Bool}
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a b) :
    ∀ z, z ∈ (parafermionicCoverRefinedPrimalSubstitute
      (w.map (parafermionicCoverBoxOpenWalkHom n A))).support →
      z ∉ (parafermionicCoverRefinedPairingWalk n hn A q).support := by
  apply parafermionicCoverRefinedPrimalSubstitute_avoidsPairingWalk
  intro d hd
  exact parafermionicCoverBoxOpenWalkHom_dart_state_true n A w d hd

end PottsContinuity.FKC.FiniteFK
