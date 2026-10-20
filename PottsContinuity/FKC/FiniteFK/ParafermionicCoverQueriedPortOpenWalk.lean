-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverQueriedPortOpenWalk.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverTwoReturnFixedLoopData
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

/-- A connection between the seed and its actual open-pair port transports to
the two primal endpoints of any retained finite port querying the same edge.
The walk is only reoriented when the unordered edge has the opposite order. -/
theorem parafermionicCoverQueriedPort_openWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hquery : parafermionicCoverPortEdge c.1 =
      parafermionicCoverFiniteEdgeEmbedding n e)
    (hconn : ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e))
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort)) :
    ∃ u v : ParafermionicAmbientVertex n,
      u.1 = parafermionicCoverPortVertex c.1 ∧
      v.1 = parafermionicCoverPortOtherVertex c.1 ∧
      Nonempty ((openGraph (ParafermionicAmbientGraph n) A).Walk u v) := by
  let u : ParafermionicAmbientVertex n :=
    parafermionicCoverFinitePortPrimalVertex n c
  have hotherMem : parafermionicCoverPortOtherVertex c.1 ∈
      (parafermionicCoverFiniteEdgeEmbedding n e).1 := by
    have hval := congrArg Subtype.val hquery
    rw [← hval, parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_right _ _
  let v : ParafermionicAmbientVertex n :=
    ⟨parafermionicCoverPortOtherVertex c.1,
      parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e _ hotherMem⟩
  have huval : parafermionicCoverBoxVertexEmbedding n u =
      parafermionicCoverPortVertex c.1 := rfl
  have hvval : parafermionicCoverBoxVertexEmbedding n v =
      parafermionicCoverPortOtherVertex c.1 := rfl
  have hselected :=
    parafermionicCoverFiniteEdgeCutSelectedEdge_eq_seedOpenPort_endpoints n hn e
  have hmap : Sym2.map (parafermionicCoverBoxVertexEmbedding n) e.1 =
      s(parafermionicCoverPortVertex c.1,
        parafermionicCoverPortOtherVertex c.1) := by
    calc
      Sym2.map (parafermionicCoverBoxVertexEmbedding n) e.1 =
          (parafermionicCoverFiniteEdgeEmbedding n e).1 := rfl
      _ = (parafermionicCoverPortEdge c.1).1 := congrArg Subtype.val hquery.symm
      _ = s(parafermionicCoverPortVertex c.1,
          parafermionicCoverPortOtherVertex c.1) :=
        parafermionicCoverPortEdge_eq_incident_pair c.1
      _ = s((parafermionicCoverBoxVertexEmbedding n) u,
          (parafermionicCoverBoxVertexEmbedding n) v) := by
        rw [huval, hvval]
  rw [← huval, ← hvval] at hmap
  have heval : e.1 = s(u, v) := by
    apply Sym2.map.injective (parafermionicCoverBoxVertexEmbedding n).injective
    simpa [Function.Embedding.sym2Map_apply] using hmap
  have hpair : s(u, v) = s(
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e),
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
    rw [← heval]
    exact hselected
  obtain ⟨p⟩ := (actualConnected_iff_walk _ _ _ _).mp hconn
  rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · refine ⟨u, v, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rw [hu, hv]
      exact ⟨p⟩
  · refine ⟨u, v, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · rw [hu, hv]
      exact ⟨p.reverse⟩

end
end PottsContinuity.FKC.FiniteFK
