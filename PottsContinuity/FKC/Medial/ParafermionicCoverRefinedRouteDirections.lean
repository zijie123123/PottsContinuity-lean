-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedRouteDirections.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPortCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCapPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

private theorem parafermionicCoverCompassNeighbor_eq_of_projection
    (u v : ParafermionicCoverVertex) (d : Fin 4)
    (hadj : parafermionicCoverGraph.Adj u v)
    (hproj : v.1 = parafermionicCoverCompassBaseNeighbor u d) :
    parafermionicCoverCompassNeighbor u d = v := by
  unfold parafermionicCoverCompassNeighbor
  exact (parafermionicCoverNeighborLift_unique u
    (parafermionicCoverCompassBaseNeighbor u d) v hproj hadj).symm

theorem parafermionicCoverRefinedLayerStep_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedPortEmbedding (c, true))
      (parafermionicCoverPortRadialCompass c) =
        parafermionicCoverRefinedPortEmbedding (c, false) := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact (parafermionicCoverRefinedPortEmbedding_layer_adj c).symm
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortRadialCompass, parafermionicCoverCompassBaseNeighbor] <;> omega

theorem parafermionicCoverRefinedOpenPairStep_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverPortRadialCompass c) =
        parafermionicCoverRefinedPortEmbedding (parafermionicCoverOpenPair c, false) := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact parafermionicCoverRefinedPortEmbedding_openPair_adj c
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortRadialCompass, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverOpenPair, LatticePort.openPair,

        ] <;> omega

theorem parafermionicCoverRefinedClosedCapStep₁_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedPortEmbedding (c, false))
      (parafermionicCoverPortCellNormalCompass c + 2) =
        parafermionicCoverRefinedClosedCapMiddle c := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact parafermionicCoverRefinedClosedCapMiddle_base_adj c
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverRefinedClosedCapMiddle_horizontal,
        parafermionicCoverRefinedClosedCapMiddle_vertical,
        parafermionicCoverPortCellNormalCompass,
        parafermionicCoverCompassBaseNeighbor] <;> omega

theorem parafermionicCoverRefinedClosedCapStep₂_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedClosedCapMiddle c)
      (parafermionicCoverPortCellNormalCompass c + 2) =
        parafermionicCoverRefinedPortEmbedding (parafermionicCoverClosedPair c, false) := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact parafermionicCoverRefinedClosedCapMiddle_closedPair_adj c
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverRefinedClosedCapMiddle_horizontal,
        parafermionicCoverRefinedClosedCapMiddle_vertical,
        parafermionicCoverPortCellNormalCompass,
        parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverClosedPair, LatticePort.closedPair] <;> omega

theorem parafermionicCoverRefinedCornerStep₁_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedPortEmbedding (c, true))
      (parafermionicCoverPortRadialCompass c + 2) =
        parafermionicCoverRefinedCornerMid₁ c := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact (parafermionicCoverRefinedCornerRoute_adj c).1
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortRadialCompass, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverCornerPair, LatticePort.cornerPair,

        ] <;> omega

theorem parafermionicCoverRefinedCornerStep₂_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedCornerMid₁ c)
      (parafermionicCoverPortRadialCompass c + 2) =
        parafermionicCoverRefinedCornerElbow c := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact (parafermionicCoverRefinedCornerRoute_adj c).2.1
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortRadialCompass, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverCornerPair, LatticePort.cornerPair,

        ] <;> omega

theorem parafermionicCoverRefinedCornerStep₃_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedCornerElbow c)
      (parafermionicCoverPortCellNormalCompass c) =
        parafermionicCoverRefinedCornerMid₂ c := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact (parafermionicCoverRefinedCornerRoute_adj c).2.2.1
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortCellNormalCompass, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverCornerPair, LatticePort.cornerPair,

        ] <;> omega

theorem parafermionicCoverRefinedCornerStep₄_compass (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor
      (parafermionicCoverRefinedCornerMid₂ c)
      (parafermionicCoverPortCellNormalCompass c) =
        parafermionicCoverRefinedPortEmbedding (parafermionicCoverCornerPair c, true) := by
  apply parafermionicCoverCompassNeighbor_eq_of_projection
  · exact (parafermionicCoverRefinedCornerRoute_adj c).2.2.2
  · rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        parafermionicCoverPortCellNormalCompass, parafermionicCoverCompassBaseNeighbor,
        parafermionicCoverCornerPair, LatticePort.cornerPair,

        ] <;> omega

end PottsContinuity.FKC.Medial
