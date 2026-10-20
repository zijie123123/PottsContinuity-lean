-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutReconnection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTerminalLabels
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance edgeCutReconnectionPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := parafermionicCoverFinitePortFintype n

local instance edgeCutReconnectionCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

local instance edgeCutReconnectionCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj := Classical.decRel _

theorem parafermionicCoverFiniteEdgeCutPort_state_eq_mem (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e) :
    parafermionicCoverPortBondState (parafermionicCoverConfigurationExtensionState n A)
      c.1 = decide (e ∈ A) := by
  have hEdge : parafermionicCoverPortEdge
      c.1 =
        parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using hc
  by_cases hmem : e ∈ A
  · have hin : parafermionicCoverFiniteEdgeEmbedding n e ∈
        parafermionicCoverConfigurationExtension n A :=
      (parafermionicCoverConfigurationExtension_inside n A e).mpr hmem
    simp [parafermionicCoverPortBondState, hEdge,
      parafermionicCoverConfigurationExtensionState, hin, hmem]
  · have hout : parafermionicCoverFiniteEdgeEmbedding n e ∉
        parafermionicCoverConfigurationExtension n A := by
      intro hm
      have hbase := (parafermionicCoverConfigurationExtension_inside n A e).mp hm
      exact hmem hbase
    simp [parafermionicCoverPortBondState, hEdge,
      parafermionicCoverConfigurationExtensionState, hout, hmem]

theorem parafermionicCoverFiniteEdgeCutPort_localPair_eq_state (n : ℕ) (_hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e) :
    (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      if e ∈ A then parafermionicCoverOpenPair c.1
      else parafermionicCoverClosedPair c.1 := by
  rw [parafermionicCoverFiniteLocalPairPerm_val, parafermionicCoverLocalPair]
  rw [parafermionicCoverFiniteEdgeCutPort_state_eq_mem n A e c hc]
  by_cases hmem : e ∈ A <;> simp [hmem]

private theorem parafermionicCoverOpenPair_closedPair_commute
    (c : ParafermionicCoverPort) :
    parafermionicCoverClosedPair (parafermionicCoverOpenPair c) =
      parafermionicCoverOpenPair (parafermionicCoverClosedPair c) := by
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases tip <;> cases side <;>
    simp [parafermionicCoverOpenPair, parafermionicCoverClosedPair,
      parafermionicCoverPortOtherVertex, LatticePort.openPair,
      LatticePort.closedPair, LatticeBond.source, LatticeBond.target,
      parafermionicCoverSheetShift] <;> rfl

theorem parafermionicCoverFiniteEdgeCutSeed_localPair_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteLocalPairPerm n A
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e) =
      if e ∈ A then
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort
      else
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort := by
  apply Subtype.ext
  rw [parafermionicCoverFiniteEdgeCutPort_localPair_eq_state n hn A e
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e)
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1]
  by_cases hmem : e ∈ A
  · simp [hmem, (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).open_eq]
  · simp [hmem, (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closed_eq]

theorem parafermionicCoverFiniteEdgeCutClosed_localPair_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteLocalPairPerm n A
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort =
      if e ∈ A then
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort
      else parafermionicCoverFiniteEdgeCutSeedPort n hn e := by
  apply Subtype.ext
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  rw [parafermionicCoverFiniteEdgeCutPort_localPair_eq_state n hn A e
    o.closedPort o.closed_queried]
  by_cases hmem : e ∈ A
  · simp only [ite_eq_left hmem]
    rw [o.closed_eq]
    exact o.openClosed_eq.symm
  · simp only [ite_eq_right hmem]
    calc
      parafermionicCoverClosedPair o.closedPort.1 =
          parafermionicCoverClosedPair (parafermionicCoverClosedPair
            (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1) :=
              congrArg parafermionicCoverClosedPair o.closed_eq
      _ = (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1 :=
            parafermionicCoverClosedPair_involutive _

theorem parafermionicCoverFiniteEdgeCutOpen_localPair_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteLocalPairPerm n A
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort =
      if e ∈ A then
        parafermionicCoverFiniteEdgeCutSeedPort n hn e
      else
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort := by
  apply Subtype.ext
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  rw [parafermionicCoverFiniteEdgeCutPort_localPair_eq_state n hn A e
    o.openPort o.open_queried]
  by_cases hmem : e ∈ A
  · simp only [ite_eq_left hmem]
    calc
      parafermionicCoverOpenPair o.openPort.1 =
          parafermionicCoverOpenPair (parafermionicCoverOpenPair
            (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1) :=
              congrArg parafermionicCoverOpenPair o.open_eq
      _ = (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1 :=
            parafermionicCoverOpenPair_involutive _
  · simp only [ite_eq_right hmem]
    calc
      parafermionicCoverClosedPair o.openPort.1 =
          parafermionicCoverClosedPair (parafermionicCoverOpenPair
            (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1) :=
              congrArg parafermionicCoverClosedPair o.open_eq
      _ = parafermionicCoverOpenPair (parafermionicCoverClosedPair
            (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1) :=
            parafermionicCoverOpenPair_closedPair_commute _
      _ = o.openClosedPort.1 := o.openClosed_eq.symm

theorem parafermionicCoverFiniteEdgeCutOpenClosed_localPair_eq (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteLocalPairPerm n A
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort =
      if e ∈ A then
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort
      else
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort := by
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  by_cases hmem : e ∈ A
  · have hpair := parafermionicCoverFiniteEdgeCutClosed_localPair_eq n hn A e
    simp only [ite_eq_left hmem] at hpair
    have hinv := parafermionicCoverFiniteLocalPairPerm_involutive n A o.closedPort
    rw [hpair] at hinv
    simpa [o, hmem] using hinv
  · have hpair := parafermionicCoverFiniteEdgeCutOpen_localPair_eq n hn A e
    simp only [ite_eq_right hmem] at hpair
    have hinv := parafermionicCoverFiniteLocalPairPerm_involutive n A o.openPort
    rw [hpair] at hinv
    simpa [o, hmem] using hinv

theorem parafermionicCoverFiniteEdgeCutQueriedPorts_eq_seedOrbit (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutQueriedPorts n e =
      {parafermionicCoverFiniteEdgeCutSeedPort n hn e,
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort,
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort,
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort} := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hseed := parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e
  have hseedEdge : parafermionicCoverPortEdge seed.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [seed, parafermionicCoverFiniteEdgeCutQueriedPorts] using hseed.1
  have horbit := parafermionicCoverPort_four_pairwise_ne seed.1
  ext d
  simp only [
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    have hdEdge : parafermionicCoverPortEdge d.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
      simpa [parafermionicCoverFiniteEdgeCutQueriedPorts] using hd
    have heq : parafermionicCoverPortEdge d.1 = parafermionicCoverPortEdge seed.1 :=
      hdEdge.trans hseedEdge.symm
    rcases (parafermionicCoverPortEdge_eq_iff_four seed.1 d.1).mp heq with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext (h.trans o.open_eq.symm)))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (h.trans o.closed_eq.symm))))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (h.trans o.openClosed_eq.symm))))
  · intro hd
    rcases hd with h | h | h | h
    · simpa [h, seed] using hseed.1
    · simpa [h, o] using o.open_queried
    · simpa [h, o] using o.closed_queried
    · simpa [h, o] using o.openClosed_queried

end
end PottsContinuity.FKC.FiniteFK
