module

public import PottsContinuity.PlanarMixed.BandActiveComparisonGeometry
public import PottsContinuity.PlanarMixed.HorizontalCrosscutGeometry
public import PottsContinuity.PlanarMixed.VerticalCrosscutGeometry

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

namespace HorizontalSquareCrosscutData
variable {a : LatticeVertex} {N : ℕ} (D : HorizontalSquareCrosscutData a N)

/-- G2 reference partition order on the literal active residual carrier. -/
theorem active_reference_partition_le (hN : 1 ≤ N)
    (B : RemovedConfiguration (rectangleGraph a N N)
      (subgraphRemovedEdges
        ((edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
          (bandArcBonds _ D.rank)).map (rankedBandEmbedding D.rank)) (rectangleGraph a N N))) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding D.rank)
      (frozenBoundary (twoBlockBoundary
        (Square.rectangleDoubleCollarInnerBottom a N N)
        (Square.rectangleDoubleCollarInnerTop a N N)
        (Square.rectangleDoubleCollarInnerBottom_disjoint_top a N N hN)) B.val)).partition ≤
      (rankedBandBoundary D.rank).partition :=
  band_active_reference_partition_le _ D.rank D.rank_edges _ _ _ D.rank_bottom D.rank_top B

/-- G2 clipping retains only sampled active bonds and original path vertices. -/
theorem active_reference_crossing_restricts (C : Configuration (rectangleGraph a N N))
    (hC : C ∈ arcsConnectionEvent (rectangleGraph a N N)
      (Square.rectangleDoubleCollarInnerBottom a N N) (Square.rectangleDoubleCollarInnerTop a N N)) :
    embeddedConfigurationRestriction
      (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank) (bandArcBonds _ D.rank)) _
      (rankedBandEmbedding D.rank) (bandActive_map_le _ D.rank) C ∈
        arcsConnectionEvent _ {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support} := by
  simpa only [rankedBandFirstArc,rankedBandSecondArc,D.rank_first_iff,D.rank_second_iff] using
    band_active_reference_crossing_restricts _ D.rank D.rank_edges _ _ D.rank_bottom D.rank_top C hC

/-- The complete active hpart uses the literal recorded open paths. -/
theorem active_reference_partition_le_frozen
    (hN : 1 ≤ N) {U : Type*} [Finite U] (H : SimpleGraph U)
    (i : RectangleVertex a N N ↪ U) (hSquare : (rectangleGraph a N N).map i ≤ H)
    (K : Configuration H)
    (hstate : D.state = embeddedConfigurationRestriction (rectangleGraph a N N) H i hSquare K)
    (ξ : BoundaryCondition U)
    (B : RemovedConfiguration (rectangleGraph a N N)
      (subgraphRemovedEdges
        ((edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
          (bandArcBonds _ D.rank)).map (rankedBandEmbedding D.rank)) (rectangleGraph a N N))) :
    (isolatedExtensionPullbackBoundary (rankedBandEmbedding D.rank)
      (frozenBoundary (twoBlockBoundary
        (Square.rectangleDoubleCollarInnerBottom a N N)
        (Square.rectangleDoubleCollarInnerTop a N N)
        (Square.rectangleDoubleCollarInnerBottom_disjoint_top a N N hN)) B.val)).partition ≤
      (isolatedExtensionPullbackBoundary ((rankedBandEmbedding D.rank).trans i)
        (frozenBoundary ξ K)).partition :=
  (D.active_reference_partition_le hN B).trans (D.frozen_boundary_order H i hSquare K hstate ξ)

end HorizontalSquareCrosscutData

namespace VerticalSquareCrosscutData
variable {a : LatticeVertex} {N : ℕ} (D : VerticalSquareCrosscutData a N)

/-- G1/G3 boundary comparison on the carrier with exposed arc bonds removed. -/
theorem active_extremalBoundaryComparison (hN : 1 ≤ N) :
    ExtremalBoundaryComparison a N hN
      (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank) (bandArcBonds _ D.rank))
      (rankedBandEmbedding D.rank) (rankedBandBoundary D.rank) :=
  band_active_reference_partition_le _ D.rank D.rank_edges _ _ _ D.rank_left D.rank_right

/-- G1/G3 crossing restriction on the same actual active carrier. -/
theorem active_squareCrossingRestrictsToArcs :
    SquareCrossingRestrictsToArcs a N
      (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank) (bandArcBonds _ D.rank))
      (rankedBandEmbedding D.rank) (bandActive_map_le _ D.rank)
      {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support} := by
  intro C hC
  simpa only [rankedBandFirstArc,rankedBandSecondArc,D.rank_first_iff,D.rank_second_iff] using
    band_active_reference_crossing_restricts _ D.rank D.rank_edges _ _ D.rank_left D.rank_right C hC

/-- The source square bound samples no already exposed internal arc bond. -/
theorem active_wiredArc_lower_bound (q : Set.Ici (1 : ℝ)) (hN : 1 ≤ N) :
    1 / (1+(q:ℝ)^2) ≤
      (measure (edgeRestriction (rankedBandGraph (rectangleGraph a N N) D.rank)
        (bandArcBonds _ D.rank)) (criticalParameters q) (rankedBandBoundary D.rank)
        (arcsConnectionEvent _ {v | v.val ∈ D.first.support}
          {v | v.val ∈ D.second.support})).toReal :=
  omega_wiredArc_lower_bound_of_extremalBoundaryComparison q a N hN _ _
    (bandActive_map_le _ D.rank) _ _ _
    (D.active_extremalBoundaryComparison hN) D.active_squareCrossingRestrictsToArcs

end VerticalSquareCrosscutData
end
end PottsContinuity.PlanarMixed
