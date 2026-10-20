-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverTwoReturnNonconnection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverOpenWalkRayEnclosure
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverQueriedPortOpenWalk
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverTwoReturnFixedLoopData
public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopCapEdge
public import PottsContinuity.FKC.Medial.ParafermionicCoverFixedLoopSeparation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

/-- In the actual closed two-return case, the seed and its open-pair port are
not connected by actual open edges. The contradiction uses the same induced
fixed loop and the same finite filling for both endpoint comparisons. -/
theorem parafermionicCoverClosedTwoReturn_not_actualConnected
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    ¬ ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e))
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := π 0
  let j := threeTerminalSwap i
  obtain ⟨hj, hfix⟩ :=
    parafermionicCoverFiniteEdgeCutClosedTwoReturn_fixedSwap n hn A e he h0 h1
  have hπj : π j = j := by
    simpa [π, j, parafermionicCoverFiniteEdgeCutRoutingSuccessor, he] using hfix
  let q := parafermionicCoverFiniteEdgeCutFixedLoop n hn A e j hj hfix
  have hq : q.IsCycle := by
    simpa [q] using
      (parafermionicCoverFiniteEdgeCutFixedLoop_isCycle n hn A e j hj hfix)
  let c : ParafermionicCoverFinitePort n :=
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π j)).1.1.1
  obtain ⟨dart, hdart, hdsink, _, _, _, hdquery, _⟩ :=
    parafermionicCoverFiniteEdgeCutFixedLoop_restoredClosedDart
      n hn A e j hj hfix he
  have hcquery : parafermionicCoverPortEdge c.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [c, hdsink] using hdquery
  intro hconn
  obtain ⟨u, v, hu, hv, w⟩ :=
    parafermionicCoverQueriedPort_openWalk n hn A e c hcquery hconn
  obtain ⟨w⟩ := w
  let pu := parafermionicCoverPortVertex c.1
  let pv := parafermionicCoverPortOtherVertex c.1
  have hAdj := parafermionicCoverPortVertex_otherEndpoint_adj c.1
  let dir := parafermionicCoverCompassDirection pu pv hAdj
  obtain ⟨N, hN, hR, hP, hRay⟩ :=
    parafermionicCoverOpenWalkRay_exists_common_box n hn A q w pu dir
  have hsep := parafermionicCoverFiniteEdgeCutFixedLoop_separatesActualPortFaces
    n hn A e j hj hfix he N hN
      (by simpa [q] using hR)
      (by simpa [c, pu, pv, dir] using hRay)
  have hiff := parafermionicCoverOpenWalkFilling_endpoint_iff
    n hn A q hq w N hN hR hP
  have hcenterU : parafermionicCoverRefinedCoarseCenter
      (parafermionicCoverBoxOpenWalkHom n A u) =
      parafermionicCoverRefinedCoarseCenter pu := by
    change parafermionicCoverRefinedCoarseCenter u.1 = _
    rw [hu]
  have hcenterV : parafermionicCoverRefinedCoarseCenter
      (parafermionicCoverBoxOpenWalkHom n A v) =
      parafermionicCoverRefinedCoarseCenter pv := by
    change parafermionicCoverRefinedCoarseCenter v.1 = _
    rw [hv]
  have hiff' := hiff
  rw [hcenterU, hcenterV] at hiff'
  apply hsep
  exact hiff'

end
end PottsContinuity.FKC.FiniteFK
