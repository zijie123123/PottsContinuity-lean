-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedSourceEndpointTurns.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedForwardRouteTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverOriginCorner
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis LatticeBond LatticePort

theorem parafermionicCoverOriginCornerPort_tangentCompass :
    parafermionicCoverPortTangentCompass parafermionicCoverOriginCornerPort = 0 := by
  norm_num [parafermionicCoverPortTangentCompass,
    parafermionicCoverOriginCornerPort, parafermionicCoverIncomingPrimalLeft,
    parafermionicCoverPortRadialCompass, medialIncomingPrimalLeft,
    LatticePort.position, LatticePort.primalVertex, LatticeBond.endpoint,
    LatticeBond.source, LatticeBond.target]

theorem parafermionicCoverOriginCornerPort_tangentPhase :
    parafermionicCoverPortTangentPhase parafermionicCoverOriginCornerPort = 0 := by
  norm_num [parafermionicCoverPortTangentPhase,
    parafermionicCoverOriginCornerPort, parafermionicCoverIncomingPrimalLeft,
    medialIncomingPrimalLeft, LatticePort.position, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target]

private theorem originCorner_incoming_true :
    parafermionicCoverIncomingPrimalLeft parafermionicCoverOriginCornerPort = true := by
  norm_num [parafermionicCoverOriginCornerPort, parafermionicCoverIncomingPrimalLeft,
    medialIncomingPrimalLeft, LatticePort.position, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target]

private theorem originCorner_radial :
    parafermionicCoverPortRadialCompass parafermionicCoverOriginCornerPort = 0 := by
  rfl

private theorem originCorner_normal :
    parafermionicCoverPortCellNormalCompass parafermionicCoverOriginCornerPort = 3 := by
  rfl

theorem parafermionicCoverOriginCornerPortOther_tangentCompass :
    parafermionicCoverPortTangentCompass parafermionicCoverOriginCornerPortOther = 1 := by
  change parafermionicCoverPortTangentCompass
    (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) = 1
  rw [parafermionicCoverPortTangentCompass,
    parafermionicCoverIncomingPrimalLeft_cornerPair, originCorner_incoming_true,
    parafermionicCoverPortRadialCompass_cornerPair, originCorner_normal]
  norm_num

theorem parafermionicCoverOriginCornerPortOther_tangentPhase :
    parafermionicCoverPortTangentPhase parafermionicCoverOriginCornerPortOther = 1 := by
  change parafermionicCoverPortTangentPhase
    (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) = 1
  rw [parafermionicCoverPortTangentPhase,
    parafermionicCoverIncomingPrimalLeft_cornerPair, originCorner_incoming_true]
  rfl

theorem parafermionicCoverOriginCornerPortOther_cornerWalk_compassDirections :
    parafermionicCoverWalkCompassDirections
      (parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther) =
      [1, 1, 0, 0] := by
  rw [parafermionicCoverRefinedCornerWalk_compassDirections]
  change [parafermionicCoverPortRadialCompass
      (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) + 2,
      parafermionicCoverPortRadialCompass
        (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort) + 2,
      parafermionicCoverPortCellNormalCompass
        (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort),
      parafermionicCoverPortCellNormalCompass
        (parafermionicCoverCornerPair parafermionicCoverOriginCornerPort)] = _
  rw [parafermionicCoverPortRadialCompass_cornerPair,
    parafermionicCoverPortCellNormalCompass_cornerPair,
    originCorner_normal, originCorner_radial]
  norm_num

end PottsContinuity.FKC.Medial
