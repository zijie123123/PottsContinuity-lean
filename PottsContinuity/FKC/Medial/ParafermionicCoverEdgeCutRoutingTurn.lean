-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutRoutingTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutRoutingWalk
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutSegmentTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

private theorem parafermionicCoverFinitePairingWalkTurn_copy
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v u' v' : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hu : u = u') (hv : v = v') :
    parafermionicCoverFinitePairingWalkTurn n hn A (p.copy hu hv) =
      parafermionicCoverFinitePairingWalkTurn n hn A p := by
  simp [parafermionicCoverFinitePairingWalkTurn, SimpleGraph.Walk.darts_copy]

theorem parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i := by
  unfold parafermionicCoverFiniteEdgeCutSourcePath_cornerCut
    parafermionicCoverFiniteEdgeCutSourceSegmentTurn
  dsimp only
  apply parafermionicCoverFinitePairingWalkTurn_copy

local instance routingTurnPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance routingTurnCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj := Classical.decRel _

theorem parafermionicCoverFiniteEdgeCutRoutingRestoredTurn
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i ≠ 0) :
    parafermionicCoverFinitePairingStepTurn n A
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1)
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e
        (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i)).1.1) =
      if e ∈ A then -1 else 1 := by
  have hπ : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i ≠ 0 := by
    intro hz
    apply hi
    by_cases he : e ∈ A
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply, threeTerminalSwap_zero, hz]
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he, hz]
  have htarget : (if e ∈ A then threeTerminalSwap
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)
    else parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) =
      parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i := by
    by_cases he : e ∈ A
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he,
        openRoutingSuccessor_apply]
    · simp [parafermionicCoverFiniteEdgeCutRoutingSuccessor, he]
  rw [← htarget]
  exact (parafermionicCoverFiniteEdgeCutRestoredSinkEdge_forward_turn n hn A e
    (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i) hπ).2.2

private theorem parafermionicCoverFinitePairingWalkTurn_splice
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {s u v t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk s u)
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk v t)
    (hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteEdgeCutRoutingSplice p q hadj) =
      parafermionicCoverFinitePairingWalkTurn n hn A p +
        parafermionicCoverFinitePairingStepTurn n A u v +
        parafermionicCoverFinitePairingWalkTurn n hn A q := by
  simp [parafermionicCoverFiniteEdgeCutRoutingSplice,
    parafermionicCoverFinitePairingWalkTurn,
    SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, add_assoc]

theorem parafermionicCoverFiniteEdgeCutRoutingWalk_turn_twoSegments
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let i := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e 0 +
        (if e ∈ A then -1 else 1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
  rw [parafermionicCoverFiniteEdgeCutRoutingWalk_twoSegments n hn A e h0 h1]
  dsimp
  rw [parafermionicCoverFinitePairingWalkTurn_copy,
    parafermionicCoverFinitePairingWalkTurn_splice]
  rw [parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e 0 h0,
    ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e 0,
    ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e i]

theorem parafermionicCoverFiniteEdgeCutRoutingWalk_turn_threeSegments
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let i := r 0
    let j := r i
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e 0 +
        (if e ∈ A then -1 else 1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i +
        (if e ∈ A then -1 else 1) +
        parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e j := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let i := r 0
  let j := r i
  rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
  rw [parafermionicCoverFiniteEdgeCutRoutingWalk_threeSegments n hn A e h0 h1]
  dsimp
  rw [parafermionicCoverFinitePairingWalkTurn_copy,
    parafermionicCoverFinitePairingWalkTurn_splice,
    parafermionicCoverFinitePairingWalkTurn_splice]
  rw [parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e 0 h0,
    parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e i h1,
    ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e 0,
    ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e i,
    ← parafermionicCoverFiniteEdgeCutSourceCornerTurn_eq_segment n hn A e j]
  ring

end
end PottsContinuity.FKC.FiniteFK
