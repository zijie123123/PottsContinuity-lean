/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutReconnectionTurn.lean`.
Adaptation: namespace/import relocation; canonical seed labels.
-/
module

public import PottsContinuity.Thm4.EdgeCutReconnection
public import PottsContinuity.Thm4.WalkTurn
public import PottsContinuity.Thm4.ThreeTerminalRouting
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
open SimpleGraph
noncomputable section

local instance edgeCutTurnPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := parafermionicCoverFinitePortFintype n

local instance edgeCutTurnCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj :=
  Classical.decRel _

private theorem medialTurnPositive_eq_incoming_xor_state
    (ω : LatticeBond → Bool) (p : LatticePort) :
    medialTurnPositive ω p = (medialIncomingPrimalLeft p != ω p.bond) := by
  rcases p with ⟨⟨⟨x, y⟩, axis⟩, tip, side⟩
  cases axis with
  | horizontal =>
      cases tip <;> cases side <;>
        cases hstate : ω ⟨(x, y), LatticeAxis.horizontal⟩ <;>
        simp [medialTurnPositive, medialIncomingPrimalLeft, hstate]
  | vertical =>
      cases tip <;> cases side <;>
        cases hstate : ω ⟨(x, y), LatticeAxis.vertical⟩ <;>
        simp [medialTurnPositive, medialIncomingPrimalLeft, hstate]

private theorem parafermionicCoverFiniteEdgeCutSinkTurnExponent
    (n : ℕ) (_hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e)
    (hin : parafermionicCoverIncomingPrimalLeft c.1 = true) :
    parafermionicCoverMedialTurnExponent
        (parafermionicCoverConfigurationExtensionState n A) c.1 =
      if e ∈ A then -1 else 1 := by
  have hstate := parafermionicCoverFiniteEdgeCutPort_state_eq_mem n A e c hc
  unfold parafermionicCoverMedialTurnExponent parafermionicCoverMedialTurnPositive
  rw [medialTurnPositive_eq_incoming_xor_state,
    parafermionicCoverPortLocalBaseState_at, hstate]
  change (if medialIncomingPrimalLeft c.1.1 != decide (e ∈ A) then (1 : ℤ) else -1) =
    if e ∈ A then -1 else 1
  change medialIncomingPrimalLeft c.1.1 = true at hin
  by_cases he : e ∈ A <;> simp [he, hin]

@[simp] private theorem edgeCutTurn_sink_one_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1 =
      (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false) := by
  rfl

@[simp] private theorem edgeCutTurn_sink_two_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false) := by
  rfl

@[simp] private theorem edgeCutTurn_source_one_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) := by
  rfl

@[simp] private theorem edgeCutTurn_source_two_point (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2).1.1 =
      ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := by
  rfl

private theorem edgeCutTurn_sink_one_incoming (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverIncomingPrimalLeft
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1 = true := by
  have hnot := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).2
  change ¬ (false = parafermionicCoverIncomingPrimalLeft
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1) at hnot
  cases h : parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1 <;> simp_all

private theorem edgeCutTurn_sink_two_incoming (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverIncomingPrimalLeft
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1 = true := by
  have hnot := (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).2
  change ¬ (false = parafermionicCoverIncomingPrimalLeft
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1) at hnot
  cases h : parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1 <;> simp_all

private theorem edgeCutTurn_sink_one_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hp : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1).1.1.1 =
      parafermionicCoverFiniteEdgeCutSeedPort n hn e :=
    congrArg Prod.fst (edgeCutTurn_sink_one_point n hn e)
  rw [hp]
  exact (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1

private theorem edgeCutTurn_sink_two_queried (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1 ∈
      parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  have hp : (parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2).1.1.1 =
      (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort :=
    congrArg Prod.fst (edgeCutTurn_sink_two_point n hn e)
  rw [hp]
  exact (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosed_queried

theorem parafermionicCoverFiniteEdgeCutRestoredSinkEdge_forward_turn
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (j : ThreeTerminal) (hj : j ≠ 0) :
    let k := if e ∈ A then threeTerminalSwap j else j
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1)
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e k).1.1) ∧
      parafermionicCoverFinitePairingForward n hn A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1)
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e k).1.1) ∧
      parafermionicCoverFinitePairingStepTurn n A
        ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e j).1.1)
        ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e k).1.1) =
          if e ∈ A then -1 else 1 := by
  dsimp
  have hjcases : j = 1 ∨ j = 2 := by
    fin_cases j <;> simp_all
  rcases hjcases with rfl | rfl
  · by_cases he : e ∈ A
    · simp only [ite_eq_left he, threeTerminalSwap_one]
      rw [edgeCutTurn_sink_one_point, edgeCutTurn_source_two_point]
      have hpair := parafermionicCoverFiniteEdgeCutSeed_localPair_eq n hn A e
      simp only [ite_eq_left he] at hpair
      have hin := edgeCutTurn_sink_one_incoming n hn e
      have hq := edgeCutTurn_sink_one_queried n hn e
      have hforward : parafermionicCoverFinitePairingForward n hn A
          (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false)
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := by
        simp only [parafermionicCoverFinitePairingForward]
        exact ⟨hin, hpair⟩
      refine ⟨parafermionicCoverFinitePairingForward_implies_adj n hn A hforward,
        hforward, ?_⟩
      simp only [parafermionicCoverFinitePairingStepTurn]
      have ht := parafermionicCoverFiniteEdgeCutSinkTurnExponent n hn A e
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e) hq hin
      simpa [he] using ht
    · simp only [ite_eq_right he]
      rw [edgeCutTurn_sink_one_point, edgeCutTurn_source_one_point]
      have hpair := parafermionicCoverFiniteEdgeCutSeed_localPair_eq n hn A e
      simp only [ite_eq_right he] at hpair
      have hin := edgeCutTurn_sink_one_incoming n hn e
      have hq := edgeCutTurn_sink_one_queried n hn e
      have hforward : parafermionicCoverFinitePairingForward n hn A
          (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false)
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) := by
        simp only [parafermionicCoverFinitePairingForward]
        exact ⟨hin, hpair⟩
      refine ⟨parafermionicCoverFinitePairingForward_implies_adj n hn A hforward,
        hforward, ?_⟩
      simp only [parafermionicCoverFinitePairingStepTurn]
      have ht := parafermionicCoverFiniteEdgeCutSinkTurnExponent n hn A e
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e) hq hin
      simpa [he] using ht
  · by_cases he : e ∈ A
    · simp only [ite_eq_left he, threeTerminalSwap_two]
      rw [edgeCutTurn_sink_two_point, edgeCutTurn_source_one_point]
      have hpair := parafermionicCoverFiniteEdgeCutOpenClosed_localPair_eq n hn A e
      simp only [ite_eq_left he] at hpair
      have hin := edgeCutTurn_sink_two_incoming n hn e
      have hq := edgeCutTurn_sink_two_queried n hn e
      have hforward : parafermionicCoverFinitePairingForward n hn A
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false)
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).closedPort, false) := by
        simp only [parafermionicCoverFinitePairingForward]
        exact ⟨hin, hpair⟩
      refine ⟨parafermionicCoverFinitePairingForward_implies_adj n hn A hforward,
        hforward, ?_⟩
      simp only [parafermionicCoverFinitePairingStepTurn]
      have ht := parafermionicCoverFiniteEdgeCutSinkTurnExponent n hn A e
        ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort) hq hin
      simpa [he] using ht
    · simp only [ite_eq_right he]
      rw [edgeCutTurn_sink_two_point, edgeCutTurn_source_two_point]
      have hpair := parafermionicCoverFiniteEdgeCutOpenClosed_localPair_eq n hn A e
      simp only [ite_eq_right he] at hpair
      have hin := edgeCutTurn_sink_two_incoming n hn e
      have hq := edgeCutTurn_sink_two_queried n hn e
      have hforward : parafermionicCoverFinitePairingForward n hn A
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false)
          ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort, false) := by
        simp only [parafermionicCoverFinitePairingForward]
        exact ⟨hin, hpair⟩
      refine ⟨parafermionicCoverFinitePairingForward_implies_adj n hn A hforward,
        hforward, ?_⟩
      simp only [parafermionicCoverFinitePairingStepTurn]
      have ht := parafermionicCoverFiniteEdgeCutSinkTurnExponent n hn A e
        ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort) hq hin
      simpa [he] using ht

end
end PottsContinuity.Thm4
