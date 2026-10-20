-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverEdgeCutSinkPhase.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEdgeCutSuffixPhase
public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhaseRecurrence
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial SimpleGraph
noncomputable section

/-- The first restored splice dart gives the actual sink-to-next-source
phase relation in a two-segment routing. -/
theorem parafermionicCoverPathPhaseAtom_routing_two_sink
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) = 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π 0)).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        ((if e ∈ A then -1 else 1 : ℤ) : ℝ))) *
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1 := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let p0 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0
  let p1 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  let hadj := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0
  let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 p1 hadj
  have hπi : π i = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e i
      (by simpa [r, i] using h1)
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e i hπi
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_twoSegments n hn A e h0 h1
  have hfull : parafermionicCoverFiniteOriginExplorationPath n hn A =
      route.copy hs ht := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    simpa [route, p0, p1, hadj, i, r] using hroute
  let d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart :=
    ⟨((parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π 0)).1.1,
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1), hadj⟩
  have hdart : d ∈ route.darts := by
    simp [d, route, p0, p1, i, r, π,
      parafermionicCoverFiniteEdgeCutRoutingSplice, Walk.darts_append,
      Walk.darts_cons]
  have hdartCopy : d ∈ (route.copy hs ht).darts := by
    simpa [Walk.darts_copy] using hdart
  have hmem : d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts :=
    hfull.symm ▸ hdartCopy
  have hrec := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d hmem
  have hturn := parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e 0 h0
  rw [hturn] at hrec
  simpa [d, r, π] using hrec

/-- The first two restored splice darts give both actual sink-to-next-source
phase relations in a three-segment routing. -/
theorem parafermionicCoverPathPhaseAtom_routing_three_sinks
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (h0 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
      (parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e 0) ≠ 0) :
    let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
    let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π 0)).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        ((if e ∈ A then -1 else 1 : ℤ) : ℝ))) *
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1 ∧
    parafermionicCoverPathPhaseAtom q n hn A
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (π (r 0))).1.1 =
      Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
        ((if e ∈ A then -1 else 1 : ℤ) : ℝ))) *
        parafermionicCoverPathPhaseAtom q n hn A
          (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r (r 0))).1.1 := by
  let r := parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e
  let π := parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
  let i := r 0
  let j := r i
  let p0 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e 0
  let p1 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  let p2 := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e j
  let hadj01 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e 0 h0
  let hadj12 := parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i h1
  let inner := parafermionicCoverFiniteEdgeCutRoutingSplice p1 p2 hadj12
  let route := parafermionicCoverFiniteEdgeCutRoutingSplice p0 inner hadj01
  have hreturn := parafermionicCoverFiniteEdgeCutRoutingSuccessor_three_return r h0 h1
  have hπj : π j = 0 :=
    parafermionicCoverFiniteEdgeCutRoutingSuccessor_zero_terminal n hn A e j
      (by simpa [r, i, j] using hreturn)
  have hs := parafermionicCoverFiniteEdgeCutSourceLabel_zero_point n hn A e
  have ht := parafermionicCoverFiniteEdgeCutSinkLabel_zero_point n hn A e j hπj
  have hroute := parafermionicCoverFiniteEdgeCutRoutingWalk_threeSegments n hn A e h0 h1
  have hfull : parafermionicCoverFiniteOriginExplorationPath n hn A =
      route.copy hs ht := by
    rw [← parafermionicCoverFiniteEdgeCutRoutingWalk_eq_originExploration n hn A e]
    simpa [route, inner, p0, p1, p2, hadj01, hadj12, i, j, r] using hroute
  let d0 : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart :=
    ⟨((parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π 0)).1.1,
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r 0)).1.1), hadj01⟩
  let d1 : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart :=
    ⟨((parafermionicCoverFiniteEdgeCutSinkLabels n hn e (π i)).1.1,
      (parafermionicCoverFiniteEdgeCutSourceLabels n hn e (r i)).1.1), hadj12⟩
  have hdart0 : d0 ∈ route.darts := by
    simp [d0, route, inner, p0, p1, p2, i, j, r, π,
      parafermionicCoverFiniteEdgeCutRoutingSplice, Walk.darts_append,
      Walk.darts_cons]
  have hdart1 : d1 ∈ route.darts := by
    simp [d1, route, inner, p0, p1, p2, i, j, r, π,
      parafermionicCoverFiniteEdgeCutRoutingSplice, Walk.darts_append,
      Walk.darts_cons]
  have hdartCopy0 : d0 ∈ (route.copy hs ht).darts := by
    simpa [Walk.darts_copy] using hdart0
  have hdartCopy1 : d1 ∈ (route.copy hs ht).darts := by
    simpa [Walk.darts_copy] using hdart1
  have hmem0 : d0 ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts :=
    hfull.symm ▸ hdartCopy0
  have hmem1 : d1 ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts :=
    hfull.symm ▸ hdartCopy1
  have hrec0 := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d0 hmem0
  have hrec1 := parafermionicCoverPathPhaseAtom_darts_recurrence q n hn A d1 hmem1
  have hturn0 := parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e 0 h0
  have hturn1 := parafermionicCoverFiniteEdgeCutRoutingRestoredTurn n hn A e i h1
  rw [hturn0] at hrec0
  rw [hturn1] at hrec1
  constructor
  · simpa [d0, r, π, i, j] using hrec0
  · simpa [d1, r, π, i, j] using hrec1

end
end PottsContinuity.FKC.FiniteFK
