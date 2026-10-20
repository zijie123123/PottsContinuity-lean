-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverSourceTurning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedForwardWalkTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverDirectedPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceEndpointTurns
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceClosureTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourcePositiveTurning
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open SimpleGraph

theorem parafermionicCoverRefinedOriginExplorationPath_turn_identity
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverCompassLinearTurnSum
      ([0] ++ parafermionicCoverWalkCompassDirections
        (parafermionicCoverRefinedPairingWalk n hn A
          (parafermionicCoverFiniteOriginExplorationPath n hn A)) ++ [1]) =
      parafermionicCoverFinitePairingWalkTurn n hn A
        (parafermionicCoverFiniteOriginExplorationPath n hn A) + 1 := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hforward := parafermionicCoverFiniteCornerCut_isPath_forward n hn A
  have hgeneral := parafermionicCoverRefinedForwardWalkTurn_identity n hn A p hforward
  have hstartCompass : parafermionicCoverPortTangentCompass
      parafermionicCoverOriginCornerPort = 0 :=
    parafermionicCoverOriginCornerPort_tangentCompass
  have hstartPhase : parafermionicCoverPortTangentPhase
      parafermionicCoverOriginCornerPort = 0 :=
    parafermionicCoverOriginCornerPort_tangentPhase
  have hendCompass : parafermionicCoverPortTangentCompass
      (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) = 1 := by
    change parafermionicCoverPortTangentCompass parafermionicCoverOriginCornerPortOther = 1
    exact parafermionicCoverOriginCornerPortOther_tangentCompass
  have hendPhase : parafermionicCoverPortTangentPhase
      (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) = 1 := by
    change parafermionicCoverPortTangentPhase parafermionicCoverOriginCornerPortOther = 1
    exact parafermionicCoverOriginCornerPortOther_tangentPhase
  simpa [p, parafermionicCoverFiniteOriginCornerPort_val,
    parafermionicCoverFiniteCornerPairPerm_origin,
    hstartCompass, hstartPhase, hendCompass, hendPhase] using hgeneral

theorem parafermionicCoverFiniteOriginExplorationPath_turn_eq_four
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverFinitePairingWalkTurn n hn A
      (parafermionicCoverFiniteOriginExplorationPath n hn A) = 4 := by
  have hpad := parafermionicCoverRefinedOriginExplorationPath_turn_identity n hn A
  have hclosure := parafermionicCoverRefinedSourceCycle_turn_eq_paddedSourcePath n hn A
  have hpositive := parafermionicCoverRefinedSourceCycle_cyclicCompassTurn_eq_four n hn A
  calc
    parafermionicCoverFinitePairingWalkTurn n hn A
        (parafermionicCoverFiniteOriginExplorationPath n hn A) =
      parafermionicCoverCompassLinearTurnSum
        ([0] ++ parafermionicCoverWalkCompassDirections
          (parafermionicCoverRefinedPairingWalk n hn A
            (parafermionicCoverFiniteOriginExplorationPath n hn A)) ++ [1]) - 1 := by
      rw [hpad]
      ring
    _ = parafermionicCoverWalkCyclicCompassTurn
        (parafermionicCoverRefinedSourceCycle n hn A) := hclosure.symm
    _ = 4 := hpositive

end PottsContinuity.FKC.Medial
