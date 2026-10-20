/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarLaw.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarPartition
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

noncomputable section

/-- Conditioning the actual outer free FK law on the exact state of every
removed collar edge, then restricting to the inner graph, gives the FK law
with bottom and top wired separately. -/
theorem rectangleDoubleCollar_conditional_law_map
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) (q : Parameters) :
    (((law (rectangleDoubleCollarOuterGraph a w h) q
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))).filter
      (frozenStateEvent (rectangleDoubleCollarRemoved a w h)
        (rectangleDoubleCollarState a w h))
      (frozenStateEvent_support q
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
        (rectangleDoubleCollarRemoved a w h)
        (rectangleDoubleCollarState a w h))).map
      (embeddedConfigurationRestriction
        (rectangleDoubleCollarInnerGraph a w h)
        (rectangleDoubleCollarOuterGraph a w h)
        (rectangleDoubleCollarEmbedding a w h)
        (rectangleDoubleCollar_map_le a w h))) =
      law (rectangleDoubleCollarInnerGraph a w h) q
        (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
          (rectangleDoubleCollarInnerTop a w h)
          (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh)) := by
  let G := rectangleDoubleCollarInnerGraph a w h
  let H := rectangleDoubleCollarOuterGraph a w h
  let f := rectangleDoubleCollarEmbedding a w h
  have hGH : G.map f ≤ H := rectangleDoubleCollar_map_le a w h
  have hconditional := law_filter_frozen_map_embeddedRestriction G H f hGH q
    (BoundaryCondition.free (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
    (rectangleDoubleCollarState a w h)
  have hpartition := rectangleDoubleCollar_frozen_pullback_partition_eq_twoBlocks
    a w h hh
  have hlaw := law_eq_of_boundary_partition_eq (G := G) q _ _ hpartition
  calc
    (((law (rectangleDoubleCollarOuterGraph a w h) q
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))).filter
      (frozenStateEvent (rectangleDoubleCollarRemoved a w h)
        (rectangleDoubleCollarState a w h))
      (frozenStateEvent_support q
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
        (rectangleDoubleCollarRemoved a w h)
        (rectangleDoubleCollarState a w h))).map
      (embeddedConfigurationRestriction
        (rectangleDoubleCollarInnerGraph a w h)
        (rectangleDoubleCollarOuterGraph a w h)
        (rectangleDoubleCollarEmbedding a w h)
        (rectangleDoubleCollar_map_le a w h))) =
      law G q
        (isolatedExtensionPullbackBoundary f
          (frozenBoundary
            (BoundaryCondition.free
              (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
            (rectangleDoubleCollarState a w h).val)) := by
        simpa [G, H, f, rectangleDoubleCollarRemoved,
          rectangleDoubleCollarInnerGraph, rectangleDoubleCollarOuterGraph] using hconditional
    _ = law G q
        (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
          (rectangleDoubleCollarInnerTop a w h)
          (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh)) := hlaw

end
end PottsContinuity.PlanarMixed.Square
