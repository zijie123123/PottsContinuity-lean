module

public import PottsContinuity.PlanarMixed.SquareCrosscutData
public import PottsContinuity.PlanarMixed.OrderedCutConsumers

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

namespace SquareCrosscutData
variable {N : ℕ} (D : SquareCrosscutData N)

/-- Every exterior configuration respects the two distinct path classes. -/
theorem extremalBoundaryComparison (hN : 1 ≤ N) :
    ExtremalBoundaryComparison (0,0) N hN
      (rankedBandGraph (rectangleGraph (0,0) N N) D.rank)
      (rankedBandEmbedding D.rank) (rankedBandBoundary D.rank) :=
  rankedBand_extremalBoundaryComparison (0,0) N hN D.rank
    (orderedCutRank_edges D.orderedCuts) (orderedCutRank_left D.orderedCuts)
    (orderedCutRank_right D.orderedCuts)

/-- A sampled horizontal square crossing clips to the original path supports. -/
theorem squareCrossingRestrictsToArcs :
    SquareCrossingRestrictsToArcs (0,0) N
      (rankedBandGraph (rectangleGraph (0,0) N N) D.rank)
      (rankedBandEmbedding D.rank) (rankedBandGraph_map_le _ D.rank)
      {v | v.val ∈ D.first.support} {v | v.val ∈ D.second.support} := by
  simpa only [rankedBandFirstArc, rankedBandSecondArc,
    D.rank_first_iff, D.rank_second_iff] using
    rankedBand_squareCrossingRestrictsToArcs (0,0) N D.rank
      (orderedCutRank_edges D.orderedCuts) (orderedCutRank_left D.orderedCuts)
      (orderedCutRank_right D.orderedCuts)

/-- Concrete crosscut geometry removes all square-comparison premises.
The actual fibre law and any extra inherited wiring remain explicit. -/
theorem conditional_arc_lower_bound_of_fiberLaw
    {U : Type*} [Finite U] (q : Set.Ici (1 : ℝ)) (hN : 1 ≤ N)
    (η : BoundaryCondition (rankedBandVertices D.rank))
    (hη : (rankedBandBoundary D.rank).partition ≤ η.partition)
    (H : SimpleGraph U) (ξ : BoundaryCondition U)
    (F : Set (Configuration H))
    (hF : ∃ ω ∈ F, ω ∈ (law H (criticalParameters q) ξ).support)
    (s : Configuration H → Configuration (rankedBandGraph (rectangleGraph (0,0) N N) D.rank))
    (hlaw : ExtremalConditionalLaw q H
      (rankedBandGraph (rectangleGraph (0,0) N N) D.rank) ξ η F hF s) :
    1 / (1 + (q : ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter F hF).toMeasure
        (s ⁻¹' arcsConnectionEvent _ {v | v.val ∈ D.first.support}
          {v | v.val ∈ D.second.support})).toReal :=
  orderedCuts_conditional_lower_bound_of_fiberLaw q (0,0) N hN
    _ _ D.orderedCuts η hη H ξ F hF s hlaw

end SquareCrosscutData
end
end PottsContinuity.PlanarMixed
