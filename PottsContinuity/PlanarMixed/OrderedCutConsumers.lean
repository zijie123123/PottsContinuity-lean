module

public import PottsContinuity.PlanarMixed.OrderedCutBands
public import PottsContinuity.PlanarMixed.OmegaConditional
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Ordered-cut estimates on actual conditional and remaining FK laws

The only topology input is the three deterministic walk-separation statements
in OrderedCutPair. Labels, exterior partition control, and crossing restriction
are constructed and proved. The identification of the conditional law on a
record fiber with the band law (`ExtremalConditionalLaw`) is the hypothesis
`hlaw`. Additional inherited boundary wiring is allowed.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

section
variable (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
variable (A C : Set (RectangleVertex a N N))
variable (hcuts : OrderedCutPair (rectangleGraph a N N)
  (Square.squareLeftArc a N) (Square.squareRightArc a N) A C)

include hN

local notation "rank" => orderedCutRank (rectangleGraph a N N)
  (Square.squareLeftArc a N) (Square.squareRightArc a N) A C hcuts

/-- Form on a conditioned record fiber, allowing all additional inherited wiring.
The fiber law is the hypothesis `hlaw`. -/
theorem orderedCuts_conditional_lower_bound_of_fiberLaw
    {U : Type*} [Finite U]
    (η : BoundaryCondition (rankedBandVertices rank))
    (hη : (rankedBandBoundary rank).partition ≤ η.partition)
    (H : SimpleGraph U) (ξ : BoundaryCondition U)
    (F : Set (Configuration H))
    (hF : ∃ ω ∈ F, ω ∈ (law H (criticalParameters q) ξ).support)
    (s : Configuration H → Configuration (rankedBandGraph (rectangleGraph a N N) rank))
    (hlaw : ExtremalConditionalLaw q H (rankedBandGraph (rectangleGraph a N N) rank)
      ξ η F hF s) :
    1 / (1 + (q : ℝ)^2) ≤
      (((law H (criticalParameters q) ξ).filter F hF).toMeasure
        (s ⁻¹' arcsConnectionEvent _ {v | v.val ∈ A} {v | v.val ∈ C})).toReal := by
  have hboundary : ExtremalBoundaryComparison a N hN (rankedBandGraph (rectangleGraph a N N) rank)
      (rankedBandEmbedding rank) η := by
    intro K
    exact (rankedBand_extremalBoundaryComparison a N hN rank (orderedCutRank_edges hcuts)
      (orderedCutRank_left hcuts) (orderedCutRank_right hcuts) K).trans hη
  have hbound := omega_conditional_wiredArc_lower_bound_of_extremalInterfaces q a N hN
    _ _ (rankedBandGraph_map_le _ rank) _ _ η hboundary
    (rankedBand_squareCrossingRestrictsToArcs a N rank (orderedCutRank_edges hcuts)
      (orderedCutRank_left hcuts) (orderedCutRank_right hcuts)) H ξ F hF s hlaw
  simpa only [rankedBandFirstArc, rankedBandSecondArc,
    orderedCutRank_eq_one_iff, orderedCutRank_eq_three_iff] using hbound

end

end
end PottsContinuity.PlanarMixed
