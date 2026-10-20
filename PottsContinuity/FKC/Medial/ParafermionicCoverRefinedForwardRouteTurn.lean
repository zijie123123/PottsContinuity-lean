-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedForwardRouteTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationOrientation
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRoutes
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRouteInteriorShape
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedMedialStep
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open SimpleGraph

/-- The local tangent label attached to a genuine lifted port occurrence. -/
def parafermionicCoverPortTangentCompass (c : ParafermionicCoverPort) : Fin 4 :=
  if parafermionicCoverIncomingPrimalLeft c then
    parafermionicCoverPortRadialCompass c
  else parafermionicCoverPortRadialCompass c + 2

/-- The integer endpoint correction attached to a genuine lifted port occurrence. -/
def parafermionicCoverPortTangentPhase (c : ParafermionicCoverPort) : ℤ :=
  if parafermionicCoverIncomingPrimalLeft c then 0 else 1

private theorem parafermionicCoverPortCompassQuarterTurn_eq_incoming (c : ParafermionicCoverPort) :
    primalCompassQuarterTurn (parafermionicCoverPortRadialCompass c)
      (parafermionicCoverPortCellNormalCompass c) =
        if parafermionicCoverIncomingPrimalLeft c then -1 else 1 := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,sheet⟩
  cases ax <;> cases tip <;> cases side <;>
    norm_num [parafermionicCoverPortRadialCompass,
      parafermionicCoverPortCellNormalCompass,
      parafermionicCoverIncomingPrimalLeft, medialIncomingPrimalLeft,
      primalCompassQuarterTurn]

theorem parafermionicCoverRefinedForwardRoute_compassDirections
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v) :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedPairingRoute n hn A
        (parafermionicCoverFinitePairingForward_implies_adj n hn A hf)) =
      match u.2, v.2 with
      | false, false =>
          if parafermionicCoverPortBondState
              (parafermionicCoverConfigurationExtensionState n A) u.1.1 then
            [parafermionicCoverPortRadialCompass u.1.1]
          else [parafermionicCoverPortCellNormalCompass u.1.1 + 2,
            parafermionicCoverPortCellNormalCompass u.1.1 + 2]
      | true, true =>
          [parafermionicCoverPortRadialCompass u.1.1 + 2,
            parafermionicCoverPortRadialCompass u.1.1 + 2,
            parafermionicCoverPortCellNormalCompass u.1.1,
            parafermionicCoverPortCellNormalCompass u.1.1]
      | false, true => [parafermionicCoverPortRadialCompass u.1.1 + 2]
      | true, false => [parafermionicCoverPortRadialCompass u.1.1] := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  have hadj := parafermionicCoverFinitePairingForward_implies_adj n hn A hf
  cases bu <;> cases bv
  case false.false =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have hraw : parafermionicCoverLocalPair
        (parafermionicCoverConfigurationExtensionState n A) u.1 = v.1 := by
      have hval := congrArg Subtype.val hf.2
      simpa only [parafermionicCoverFiniteLocalPairPerm_val] using hval
    cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1 with
    | false =>
        have hpair : parafermionicCoverClosedPair u.1 = v.1 := by
          simpa [parafermionicCoverLocalPair, hs] using hraw
        have hwalk : parafermionicCoverRefinedPairingRoute n hn A hadj =
            (parafermionicCoverRefinedClosedCapWalk u.1).copy rfl
              (congrArg (fun c => parafermionicCoverRefinedPortEmbedding (c, false)) hpair) := by
          apply Walk.ext_support
          rw [parafermionicCoverRefinedPairingRoute_support]
          simp [parafermionicCoverRefinedPairingRouteSupport, hs, hpair,
            parafermionicCoverRefinedPairingEmbedding]
        rw [hwalk]
        simpa [parafermionicCoverWalkCompassDirections, Walk.darts_copy] using
          parafermionicCoverRefinedClosedCapWalk_compassDirections u.1
    | true =>
        have hpair : parafermionicCoverOpenPair u.1 = v.1 := by
          simpa [parafermionicCoverLocalPair, hs] using hraw
        have hwalk : parafermionicCoverRefinedPairingRoute n hn A hadj =
            (Walk.cons (parafermionicCoverRefinedPortEmbedding_openPair_adj u.1)
              Walk.nil).copy rfl
              (congrArg (fun c => parafermionicCoverRefinedPortEmbedding (c, false)) hpair) := by
          apply Walk.ext_support
          rw [parafermionicCoverRefinedPairingRoute_support]
          simp [parafermionicCoverRefinedPairingRouteSupport, hs, hpair,
            parafermionicCoverRefinedPairingEmbedding]
        rw [hwalk]
        simp only [parafermionicCoverWalkCompassDirections, Walk.darts_copy,
          Walk.darts_cons, Walk.darts_nil, List.map_cons, List.map_nil]
        apply congrArg List.singleton
        exact parafermionicCoverCompassDirection_eq_of_neighbor
          (parafermionicCoverRefinedPortEmbedding_openPair_adj u.1)
          (parafermionicCoverPortRadialCompass u.1)
          (parafermionicCoverRefinedOpenPairStep_compass u.1)
  case false.true =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have huv : u.1 = v.1 := congrArg Subtype.val hf.2
    have hwalk : parafermionicCoverRefinedPairingRoute n hn A hadj =
        (Walk.cons (parafermionicCoverRefinedPortEmbedding_layer_adj u.1)
          Walk.nil).copy rfl
            (congrArg (fun c => parafermionicCoverRefinedPortEmbedding (c, true)) huv) := by
      apply Walk.ext_support
      rw [parafermionicCoverRefinedPairingRoute_support]
      simp [parafermionicCoverRefinedPairingRouteSupport,
        parafermionicCoverRefinedPairingEmbedding, hf.2]
    rw [hwalk]
    simp only [parafermionicCoverWalkCompassDirections, Walk.darts_copy,
      Walk.darts_cons, Walk.darts_nil, List.map_cons, List.map_nil]
    apply congrArg List.singleton
    apply parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedPortEmbedding_layer_adj u.1)
    have hback := parafermionicCoverCompassNeighbor_reverse
      (parafermionicCoverRefinedPortEmbedding (u.1, true))
      (parafermionicCoverPortRadialCompass u.1)
    rw [parafermionicCoverRefinedLayerStep_compass] at hback
    exact hback
  case true.false =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have huv : u.1 = v.1 := congrArg Subtype.val hf.2
    have hwalk : parafermionicCoverRefinedPairingRoute n hn A hadj =
        (Walk.cons (parafermionicCoverRefinedPortEmbedding_layer_adj u.1).symm
          Walk.nil).copy rfl
            (congrArg (fun c => parafermionicCoverRefinedPortEmbedding (c, false)) huv) := by
      apply Walk.ext_support
      rw [parafermionicCoverRefinedPairingRoute_support]
      simp [parafermionicCoverRefinedPairingRouteSupport,
        parafermionicCoverRefinedPairingEmbedding, hf.2]
    rw [hwalk]
    simp only [parafermionicCoverWalkCompassDirections, Walk.darts_copy,
      Walk.darts_cons, Walk.darts_nil, List.map_cons, List.map_nil]
    apply congrArg List.singleton
    exact parafermionicCoverCompassDirection_eq_of_neighbor
      (parafermionicCoverRefinedPortEmbedding_layer_adj u.1).symm
      (parafermionicCoverPortRadialCompass u.1)
      (parafermionicCoverRefinedLayerStep_compass u.1)
  case true.true =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have hcorner := parafermionicCoverRefinedPairingRoute_true_true_endpoint
      n hn A u v hadj
    have hwalk : parafermionicCoverRefinedPairingRoute n hn A hadj =
        (parafermionicCoverRefinedCornerWalk u.1).copy rfl
          (congrArg (fun c => parafermionicCoverRefinedPortEmbedding (c, true))
            hcorner.symm) := by
      apply Walk.ext_support
      rw [parafermionicCoverRefinedPairingRoute_support]
      simp [parafermionicCoverRefinedPairingRouteSupport,
        parafermionicCoverRefinedPairingEmbedding, hcorner]
    rw [hwalk]
    simpa [parafermionicCoverWalkCompassDirections, Walk.darts_copy] using
      parafermionicCoverRefinedCornerWalk_compassDirections u.1

private theorem primalCompassQuarterTurn_reverse (a b : Fin 4) :
    primalCompassQuarterTurn b a = -primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> norm_num [primalCompassQuarterTurn]

private theorem primalCompassQuarterTurn_shiftFirst (a b : Fin 4) :
    primalCompassQuarterTurn (a + 2) b = -primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> norm_num [primalCompassQuarterTurn]

private theorem primalCompassQuarterTurn_shiftSecond (a b : Fin 4) :
    primalCompassQuarterTurn a (b + 2) = -primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> norm_num [primalCompassQuarterTurn]

private theorem primalCompassQuarterTurn_shiftBoth (a b : Fin 4) :
    primalCompassQuarterTurn (a + 2) (b + 2) = primalCompassQuarterTurn a b := by
  fin_cases a <;> fin_cases b <;> norm_num [primalCompassQuarterTurn]

private theorem primalCompassQuarterTurn_self (a : Fin 4) :
    primalCompassQuarterTurn a a = 0 := by
  fin_cases a <;> norm_num [primalCompassQuarterTurn]

private theorem compassLinearTurnSum_three (a b c : Fin 4) :
    parafermionicCoverCompassLinearTurnSum [a, b, c] =
      primalCompassQuarterTurn a b + primalCompassQuarterTurn b c := by
  simp [parafermionicCoverCompassLinearTurnSum]

private theorem compassLinearTurnSum_four (a b c d : Fin 4) :
    parafermionicCoverCompassLinearTurnSum [a, b, c, d] =
      primalCompassQuarterTurn a b + primalCompassQuarterTurn b c +
        primalCompassQuarterTurn c d := by
  simp [parafermionicCoverCompassLinearTurnSum]; ring

private theorem compassLinearTurnSum_six (a b c d e f : Fin 4) :
    parafermionicCoverCompassLinearTurnSum [a, b, c, d, e, f] =
      primalCompassQuarterTurn a b + primalCompassQuarterTurn b c +
        primalCompassQuarterTurn c d + primalCompassQuarterTurn d e +
        primalCompassQuarterTurn e f := by
  simp [parafermionicCoverCompassLinearTurnSum]; ring

private theorem fin4_add_two_add_two (a : Fin 4) : (a + 2) + 2 = a := by
  fin_cases a <;> decide

/-- Local tangent padding converts one oriented actual pairing edge into the
signed turn of its exact refined route, with only the endpoint phase correction. -/
theorem parafermionicCoverRefinedForwardRouteTurn_identity
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hf : parafermionicCoverFinitePairingForward n hn A u v) :
    parafermionicCoverCompassLinearTurnSum
        ([parafermionicCoverPortTangentCompass u.1.1] ++
          parafermionicCoverWalkCompassDirections
            (parafermionicCoverRefinedPairingRoute n hn A
              (parafermionicCoverFinitePairingForward_implies_adj n hn A hf)) ++
          [parafermionicCoverPortTangentCompass v.1.1]) =
      parafermionicCoverFinitePairingStepTurn n A u v +
        parafermionicCoverPortTangentPhase v.1.1 -
          parafermionicCoverPortTangentPhase u.1.1 := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  have hdirs := parafermionicCoverRefinedForwardRoute_compassDirections n hn A hf
  cases bu <;> cases bv
  all_goals simp only at hdirs ⊢
  case false.false =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have hpair : parafermionicCoverLocalPair
        (parafermionicCoverConfigurationExtensionState n A) u.1 = v.1 := by
      have hval := congrArg Subtype.val hf.2
      simpa only [parafermionicCoverFiniteLocalPairPerm_val] using hval
    cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1 with
    | false =>
        have hclosed : parafermionicCoverClosedPair u.1 = v.1 := by
          simpa [parafermionicCoverLocalPair, hs] using hpair
        have hleft := hf.1
        have hq := parafermionicCoverPortCompassQuarterTurn_eq_incoming u.1
        rw [hleft] at hq
        have hqval : primalCompassQuarterTurn (parafermionicCoverPortRadialCompass u.1)
            (parafermionicCoverPortCellNormalCompass u.1) = -1 := by simpa using hq
        have hflagR : parafermionicCoverIncomingPrimalLeft v.1 = false := by
          rw [← hclosed]
          simp [parafermionicCoverIncomingPrimalLeft_closedPair, hleft]
        have htanL : parafermionicCoverPortTangentCompass u.1 =
            parafermionicCoverPortRadialCompass u.1 := by
          simp [parafermionicCoverPortTangentCompass, hleft]
        have htanR : parafermionicCoverPortTangentCompass v.1 =
            parafermionicCoverPortRadialCompass u.1 + 2 := by
          calc
            parafermionicCoverPortTangentCompass v.1 =
                parafermionicCoverPortRadialCompass v.1 + 2 := by
              simp [parafermionicCoverPortTangentCompass, hflagR]
            _ = parafermionicCoverPortRadialCompass u.1 + 2 := by
              rw [← hclosed, parafermionicCoverPortRadialCompass_closedPair]
        have hphaseL : parafermionicCoverPortTangentPhase u.1 = 0 := by
          simp [parafermionicCoverPortTangentPhase, hleft]
        have hphaseR : parafermionicCoverPortTangentPhase v.1 = 1 := by
          simp [parafermionicCoverPortTangentPhase, hflagR]
        have hqr : primalCompassQuarterTurn (parafermionicCoverPortCellNormalCompass u.1)
            (parafermionicCoverPortRadialCompass u.1) = 1 := by
          rw [primalCompassQuarterTurn_reverse, hqval]
          norm_num
        have hsum : primalCompassQuarterTurn (parafermionicCoverPortRadialCompass u.1)
              (parafermionicCoverPortCellNormalCompass u.1 + 2) +
            primalCompassQuarterTurn (parafermionicCoverPortCellNormalCompass u.1 + 2)
              (parafermionicCoverPortCellNormalCompass u.1 + 2) +
            primalCompassQuarterTurn (parafermionicCoverPortCellNormalCompass u.1 + 2)
              (parafermionicCoverPortRadialCompass u.1 + 2) = 2 := by
          rw [primalCompassQuarterTurn_shiftSecond, primalCompassQuarterTurn_self,
            primalCompassQuarterTurn_shiftBoth, hqr, hqval]
          norm_num
        have hstep : parafermionicCoverFinitePairingStepTurn n A (u, false) (v, false) = 1 := by
          simp [parafermionicCoverFinitePairingStepTurn,
            parafermionicCoverMedialTurnExponent_eq_portCompass, hs, hqval]
        rw [hdirs]
        simp only [hs, Bool.false_eq_true, ite_false, htanL, htanR]
        change parafermionicCoverCompassLinearTurnSum
            [parafermionicCoverPortRadialCompass u.1,
              parafermionicCoverPortCellNormalCompass u.1 + 2,
              parafermionicCoverPortCellNormalCompass u.1 + 2,
              parafermionicCoverPortRadialCompass u.1 + 2] = _
        rw [compassLinearTurnSum_four, hsum, hstep, hphaseR, hphaseL]
        norm_num
    | true =>
        have hopen : parafermionicCoverOpenPair u.1 = v.1 := by
          simpa [parafermionicCoverLocalPair, hs] using hpair
        have hleft := hf.1
        have hq := parafermionicCoverPortCompassQuarterTurn_eq_incoming u.1
        rw [hleft] at hq
        have hqval : primalCompassQuarterTurn (parafermionicCoverPortRadialCompass u.1)
            (parafermionicCoverPortCellNormalCompass u.1) = -1 := by simpa using hq
        have hflagR : parafermionicCoverIncomingPrimalLeft v.1 = false := by
          rw [← hopen]
          simp [parafermionicCoverIncomingPrimalLeft_openPair, hleft]
        have htanL : parafermionicCoverPortTangentCompass u.1 =
            parafermionicCoverPortRadialCompass u.1 := by
          simp [parafermionicCoverPortTangentCompass, hleft]
        have htanR : parafermionicCoverPortTangentCompass v.1 =
            parafermionicCoverPortRadialCompass u.1 := by
          calc
            parafermionicCoverPortTangentCompass v.1 =
                parafermionicCoverPortRadialCompass v.1 + 2 := by
              simp [parafermionicCoverPortTangentCompass, hflagR]
            _ = parafermionicCoverPortRadialCompass u.1 := by
              rw [← hopen, parafermionicCoverPortRadialCompass_openPair,
                fin4_add_two_add_two]
        have hphaseL : parafermionicCoverPortTangentPhase u.1 = 0 := by
          simp [parafermionicCoverPortTangentPhase, hleft]
        have hphaseR : parafermionicCoverPortTangentPhase v.1 = 1 := by
          simp [parafermionicCoverPortTangentPhase, hflagR]
        have hstep : parafermionicCoverFinitePairingStepTurn n A (u, false) (v, false) = -1 := by
          simp [parafermionicCoverFinitePairingStepTurn,
            parafermionicCoverMedialTurnExponent_eq_portCompass, hs, hqval]
        rw [hdirs]
        simp only [hs, ite_true, htanL, htanR]
        change parafermionicCoverCompassLinearTurnSum
            [parafermionicCoverPortRadialCompass u.1,
              parafermionicCoverPortRadialCompass u.1,
              parafermionicCoverPortRadialCompass u.1] = _
        rw [compassLinearTurnSum_three, primalCompassQuarterTurn_self,
          hstep, hphaseR, hphaseL]
        norm_num
  case false.true =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    rw [hdirs, ← hf.2]
    simp [parafermionicCoverPortTangentCompass, parafermionicCoverPortTangentPhase, hf.1]
    change parafermionicCoverCompassLinearTurnSum
        [parafermionicCoverPortRadialCompass u.1 + 2,
          parafermionicCoverPortRadialCompass u.1 + 2,
          parafermionicCoverPortRadialCompass u.1 + 2] = _
    rw [compassLinearTurnSum_three, primalCompassQuarterTurn_self]
    simp [parafermionicCoverFinitePairingStepTurn]
  case true.false =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    rw [hdirs, ← hf.2]
    simp [parafermionicCoverPortTangentCompass, parafermionicCoverPortTangentPhase, hf.1]
    change parafermionicCoverCompassLinearTurnSum
        [parafermionicCoverPortRadialCompass u.1,
          parafermionicCoverPortRadialCompass u.1,
          parafermionicCoverPortRadialCompass u.1] = _
    rw [compassLinearTurnSum_three, primalCompassQuarterTurn_self]
    simp [parafermionicCoverFinitePairingStepTurn]
  case true.true =>
    simp only [parafermionicCoverFinitePairingForward] at hf
    have hcorner := parafermionicCoverRefinedPairingRoute_true_true_endpoint
      n hn A u v (parafermionicCoverFinitePairingForward_implies_adj n hn A
        (by simpa only [parafermionicCoverFinitePairingForward] using hf))
    have hleft := hf.1
    have hq := parafermionicCoverPortCompassQuarterTurn_eq_incoming u.1
    rw [hleft] at hq
    have hqval : primalCompassQuarterTurn (parafermionicCoverPortRadialCompass u.1)
        (parafermionicCoverPortCellNormalCompass u.1) = 1 := by simpa using hq
    have hflagR : parafermionicCoverIncomingPrimalLeft v.1 = true := by
      rw [hcorner]
      simp [parafermionicCoverIncomingPrimalLeft_cornerPair, hleft]
    have htanL : parafermionicCoverPortTangentCompass u.1 =
        parafermionicCoverPortRadialCompass u.1 + 2 := by
      simp [parafermionicCoverPortTangentCompass, hleft]
    have htanR : parafermionicCoverPortTangentCompass v.1 =
        parafermionicCoverPortCellNormalCompass u.1 := by
      calc
        parafermionicCoverPortTangentCompass v.1 =
            parafermionicCoverPortRadialCompass v.1 := by
          simp [parafermionicCoverPortTangentCompass, hflagR]
        _ = parafermionicCoverPortCellNormalCompass u.1 := by
          rw [hcorner, parafermionicCoverPortRadialCompass_cornerPair]
    have hphaseL : parafermionicCoverPortTangentPhase u.1 = 1 := by
      simp [parafermionicCoverPortTangentPhase, hleft]
    have hphaseR : parafermionicCoverPortTangentPhase v.1 = 0 := by
      simp [parafermionicCoverPortTangentPhase, hflagR]
    have hsum : primalCompassQuarterTurn (parafermionicCoverPortRadialCompass u.1 + 2)
        (parafermionicCoverPortCellNormalCompass u.1) = -1 := by
      rw [primalCompassQuarterTurn_shiftFirst, hqval]
    have hstep : parafermionicCoverFinitePairingStepTurn n A (u, true) (v, true) = 0 := by
      simp [parafermionicCoverFinitePairingStepTurn]
    rw [hdirs]
    simp only [htanL, htanR]
    change parafermionicCoverCompassLinearTurnSum
        [parafermionicCoverPortRadialCompass u.1 + 2,
          parafermionicCoverPortRadialCompass u.1 + 2,
          parafermionicCoverPortRadialCompass u.1 + 2,
          parafermionicCoverPortCellNormalCompass u.1,
          parafermionicCoverPortCellNormalCompass u.1,
          parafermionicCoverPortCellNormalCompass u.1] = _
    rw [compassLinearTurnSum_six, primalCompassQuarterTurn_self,
      hsum, primalCompassQuarterTurn_self, hstep, hphaseR, hphaseL]
    norm_num

end PottsContinuity.FKC.Medial
