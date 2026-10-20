-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedDirectEdges.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPortEmbedding
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

/-- The two offsets assigned to one port are actual adjacent vertices of the
infinite cover graph. -/
theorem parafermionicCoverRefinedPortEmbedding_layer_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverRefinedPortEmbedding (c, true)) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax
  · rw [parafermionicCoverRefinedPortEmbedding_horizontal x y tip side false k,
      parafermionicCoverRefinedPortEmbedding_horizontal x y tip side true k]
    cases tip <;> cases side <;>
      rw [parafermionicCoverGraph_adj_iff_cases] <;>
      simp [parafermionicCoverAdjCases] <;> omega
  · rw [parafermionicCoverRefinedPortEmbedding_vertical x y tip side false k,
      parafermionicCoverRefinedPortEmbedding_vertical x y tip side true k]
    cases tip <;> cases side <;>
      rw [parafermionicCoverGraph_adj_iff_cases] <;>
      simp [parafermionicCoverAdjCases] <;> omega

/-- The fine-grid edge between a port and its deterministic open pair is also
an actual cover-graph edge; the pairing carries the correct sheet across the
lower seam. -/
theorem parafermionicCoverRefinedPortEmbedding_openPair_adj
    (c : ParafermionicCoverPort) :
    parafermionicCoverGraph.Adj
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverRefinedPortEmbedding (parafermionicCoverOpenPair c, false)) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side
  all_goals
    simp only [parafermionicCoverOpenPair, LatticePort.openPair,
      Bool.not_false, Bool.not_true,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical]
    simp only [parafermionicCoverPortOtherVertex, parafermionicCoverSheetShift,
      LatticeBond.source, LatticeBond.target] at ⊢
    rw [parafermionicCoverGraph_adj_iff_cases]
    simp [parafermionicCoverAdjCases]
    (try split_ifs) <;> omega


end PottsContinuity.FKC.Medial
