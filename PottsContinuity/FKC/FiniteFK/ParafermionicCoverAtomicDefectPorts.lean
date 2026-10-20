-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverAtomicDefectPorts.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverDefectConfigurationSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutReconnection
public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhaseZeroTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

local instance atomicPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := Fintype.ofFinite _
local instance atomicInternalDecidable (n : ℕ) :
    DecidablePred (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverFinitePortOtherEndpointInBox n c) :=
  contourEdgeActualInternalDecidable n

private theorem queried_implies_internal (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e) :
    parafermionicCoverFinitePortOtherEndpointInBox n c := by
  have hd : parafermionicCoverPortEdge c.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using hc
  apply parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e
    (parafermionicCoverPortOtherVertex c.1)
  rw [← hd, parafermionicCoverPortEdge_eq_incident_pair]
  exact Sym2.mem_mk_right _ _

/-- The literal internal-port sum reindexes to the existing queried-port fiber. -/
private theorem atomic_internal_sum_eq_queried_sum
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (∑ c ∈ (Finset.univ : Finset {c : ParafermionicCoverFinitePort n //
      parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e),
      (if parafermionicCoverIncomingPrimalLeft c.1.1 then (1 : ℂ) else -1) *
        parafermionicCoverPathPhaseAtom q n hn A (c.1, true)) =
    (∑ c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e,
      (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
        parafermionicCoverPathPhaseAtom q n hn A (c, true)) := by
  classical
  apply Finset.sum_bij (fun c hc => c.1)
  · intro c hc
    have hd := (Finset.mem_filter.mp hc).2
    simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using hd
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro c hc
    refine ⟨⟨c, queried_implies_internal n e c hc⟩, ?_, rfl⟩
    simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using hc
  · intro c hc
    rfl

/-- The actual atomic defect is the signed four-port sum on the false layer. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_eq_seedOrbit
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false) -
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) -
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let orbit := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  rw [parafermionicCoverContourFiniteEdgeAtomicDefect,
    atomic_internal_sum_eq_queried_sum q n hn e A]
  rw [parafermionicCoverFiniteEdgeCutQueriedPorts_eq_seedOrbit n hn e]
  have hs := parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e
  have hseed : parafermionicCoverIncomingPrimalLeft seed.1 = true := hs.2
  have hopen : parafermionicCoverIncomingPrimalLeft orbit.openPort.1 = false :=
    orbit.open_incoming_false
  have hclosed : parafermionicCoverIncomingPrimalLeft orbit.closedPort.1 = false :=
    orbit.closed_incoming_false
  have hopenclosed : parafermionicCoverIncomingPrimalLeft orbit.openClosedPort.1 = true :=
    orbit.openClosed_incoming_true
  have hsOpen : seed ≠ orbit.openPort := orbit.distinct_seed_open
  have hsClosed : seed ≠ orbit.closedPort := orbit.distinct_seed_closed
  have hsOpenClosed : seed ≠ orbit.openClosedPort := orbit.distinct_seed_openClosed
  have hoClosed : orbit.openPort ≠ orbit.closedPort := orbit.distinct_open_closed
  have hoOpenClosed : orbit.openPort ≠ orbit.openClosedPort := orbit.distinct_open_openClosed
  have hcOpenClosed : orbit.closedPort ≠ orbit.openClosedPort :=
    orbit.distinct_closed_openClosed
  simp [seed, orbit, hseed, hopen, hclosed, hopenclosed,
    hsOpen, hsClosed, hsOpenClosed, hoClosed, hoOpenClosed, hcOpenClosed,
    parafermionicCoverPathPhaseAtom_false_eq_true]
  ring

theorem parafermionicCoverContourFiniteEdgeAtomicDefect_eq_terminalLabels
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A =
      parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1) +
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1) -
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1) -
        parafermionicCoverPathPhaseAtom q n hn A
          ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1) := by
  rw [parafermionicCoverContourFiniteEdgeAtomicDefect_eq_seedOrbit]
  simp [parafermionicCoverFiniteEdgeCutSinkLabels_one,
    parafermionicCoverFiniteEdgeCutSinkLabels_two,
    parafermionicCoverFiniteEdgeCutSourceLabels_one,
    parafermionicCoverFiniteEdgeCutSourceLabels_two,
    parafermionicCoverFiniteEdgeCutSinkSeedLabel,
    parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
    parafermionicCoverFiniteEdgeCutSourceClosedLabel,
    parafermionicCoverFiniteEdgeCutSourceOpenLabel,
    parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse]

end
end PottsContinuity.FKC.FiniteFK
