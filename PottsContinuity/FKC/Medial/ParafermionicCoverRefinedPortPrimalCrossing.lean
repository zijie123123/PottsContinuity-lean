-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPortPrimalCrossing.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeIntersections
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedClosedCapPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverPortCompass
public import PottsContinuity.FKC.Medial.ParafermionicCoverContourBoundary

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem parafermionicCoverPortRadialCompass_neighbor_eq
    (c : ParafermionicCoverPort) :
    parafermionicCoverCompassNeighbor (parafermionicCoverPortVertex c)
      (parafermionicCoverPortRadialCompass c) = parafermionicCoverPortOtherVertex c := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
      parafermionicCoverPortRadialCompass, parafermionicCoverPortVertex,
      parafermionicCoverPortOtherVertex, LatticeBond.source, LatticeBond.target, LatticeBond.endpoint,
      LatticePort.primalVertex, parafermionicCoverNeighborLift, parafermionicCoverSheetShift] <;> omega

/-- The closed-cap midpoint lies on the actual outgoing primal ray from its port. -/
theorem parafermionicCoverRefinedClosedCapMiddle_mem_port_primalRay
    (c : ParafermionicCoverPort) :
    parafermionicCoverRefinedClosedCapMiddle c ∈
      (parafermionicCoverRefinedPrimalEdgeWalk
        (parafermionicCoverPortVertex c)
        (parafermionicCoverCompassDirection
          (parafermionicCoverPortVertex c) (parafermionicCoverPortOtherVertex c)
          (PottsContinuity.FKC.FiniteFK.parafermionicCoverPortVertex_otherEndpoint_adj c))).support := by
  have hd := parafermionicCoverCompassDirection_eq_of_neighbor
    (PottsContinuity.FKC.FiniteFK.parafermionicCoverPortVertex_otherEndpoint_adj c)
    (parafermionicCoverPortRadialCompass c)
    (parafermionicCoverPortRadialCompass_neighbor_eq c)
  rw [hd, parafermionicCoverRefinedPrimalEdgeWalk_support]
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax with
  | horizontal =>
    cases tip with
    | false =>
      cases side <;>
        convert (parafermionicCoverRefinedPrimalEdgeWalkPoints_east_mem_of_index x y k 4 (by omega)) using 1 <;>
          simp [parafermionicCoverRefinedClosedCapMiddle_horizontal,
            parafermionicCoverPortVertex, LatticePort.primalVertex,
            LatticeBond.endpoint, LatticeBond.source, parafermionicCoverPortRadialCompass]
    | true =>
      cases side <;>
        convert (parafermionicCoverRefinedPrimalEdgeWalkPoints_west_mem_of_index (x + 1) y k 4 (by omega)) using 1 <;>
          simp [parafermionicCoverRefinedClosedCapMiddle_horizontal,
            parafermionicCoverPortVertex, LatticePort.primalVertex,
            LatticeBond.endpoint, LatticeBond.target, parafermionicCoverPortRadialCompass] <;> omega
  | vertical =>
    cases tip with
    | false =>
      cases side <;>
        convert (parafermionicCoverRefinedPrimalEdgeWalkPoints_north_mem_of_index x y k 4 (by omega)) using 1 <;>
          simp [parafermionicCoverRefinedClosedCapMiddle_vertical,
            parafermionicCoverPortVertex, LatticePort.primalVertex,
            LatticeBond.endpoint, LatticeBond.source, parafermionicCoverPortRadialCompass] <;> omega
    | true =>
      cases side <;>
        convert (parafermionicCoverRefinedPrimalEdgeWalkPoints_south_mem_of_index x (y + 1) k 4 (by omega)) using 1 <;>
          simp [parafermionicCoverRefinedClosedCapMiddle_vertical,
            parafermionicCoverPortVertex, LatticePort.primalVertex,
            LatticeBond.endpoint, LatticeBond.target, parafermionicCoverPortRadialCompass] <;> omega

/-- One of the two literal closed-cap edges is the positive perpendicular
half-edge at its midpoint. -/
theorem parafermionicCoverRefinedClosedCap_positivePerpendicularEdge_mem
    (c : ParafermionicCoverPort) :
    s(parafermionicCoverRefinedClosedCapMiddle c,
      parafermionicCoverCompassNeighbor
        (parafermionicCoverRefinedClosedCapMiddle c)
        (if c.1.bond.axis = LatticeAxis.horizontal then 1 else 0)) ∈
      (parafermionicCoverRefinedClosedCapWalk c).edges := by
  rcases c with ⟨⟨⟨⟨x,y⟩,ax⟩,tip,side⟩,k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp only [parafermionicCoverRefinedClosedCapWalk,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil] <;>
    simp [parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      parafermionicCoverCompassNeighbor, parafermionicCoverCompassBaseNeighbor,
      parafermionicCoverNeighborLift, parafermionicCoverSheetShift,
      parafermionicCoverClosedPair, LatticePort.closedPair,

      ] <;> omega

end PottsContinuity.FKC.Medial
