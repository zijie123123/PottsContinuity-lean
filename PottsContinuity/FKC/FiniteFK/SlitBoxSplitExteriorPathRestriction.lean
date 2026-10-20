-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitExteriorPathRestriction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverInteriorClosed
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem embeddedRestriction_openAdj_of_openAdj
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hGH : G.map f ≤ H) (A : Configuration H)
    {x y : V} (hxy : G.Adj x y)
    (hopen : (openGraph H A).Adj (f x) (f y)) :
    (openGraph G (embeddedConfigurationRestriction G H f hGH A)).Adj x y := by
  rw [openGraph_adj] at hopen ⊢
  rcases hopen with ⟨eH, heH, heval⟩
  let eG : G.edgeSet := ⟨s(x, y), G.mem_edgeSet.mpr hxy⟩
  have hval : (embeddedEdgeEmbedding G H f hGH eG).val = eH.val := by
    rw [embeddedEdgeEmbedding_coe]
    change Sym2.map f s(x, y) = eH.val
    rw [Sym2.map_mk]
    exact heval.symm
  have he : embeddedEdgeEmbedding G H f hGH eG = eH := Subtype.ext hval
  refine ⟨eG, ?_, rfl⟩
  exact (mem_embeddedConfigurationRestriction G H f hGH A eG).mpr (he ▸ heH)

end
end PottsContinuity.FKC.FiniteFK
