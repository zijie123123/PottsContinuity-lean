/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualCornerMarginal.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerBoundary
public import PottsContinuity.PlanarMixed.Square.RectangleDualCornerConnectivity
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial
noncomputable section

/-- The law on the actual dual rectangle, wired on its two vertical sides,
pushes forward under the literal corner restriction to a law dominated on
every increasing event by the corner graph wired on its two side columns. -/
theorem rectangleDualCorner_marginal_bound
    (a : LatticeVertex) (w h : ℕ) (q : Parameters)
    (S : Set (Configuration (rectangleDualCornerCoreGraph a w h)))
    (hS : IsUpperSet S) :
    (measure (rectangleDualGraph a w h) q
      (BoundaryCondition.wired
        (rectangleDoubleCollarDualInnerVerticalSides a w h))
      {A | rectangleDualCornerCoreConfigurationRestriction a w h A ∈ S}).toReal ≤
    (measure (rectangleDualCornerCoreGraph a w h) q
      (BoundaryCondition.wired (rectangleDualCornerSideColumns a w h)) S).toReal := by
  classical
  exact embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    (G := rectangleDualCornerCoreGraph a w h)
    (H := rectangleDualGraph a w h)
    (f := rectangleDualCornerCoreEmbedding a w h)
    (hGH := rectangleDualCornerCoreGraph_map_le_dual a w h)
    q
    (BoundaryCondition.wired
      (rectangleDoubleCollarDualInnerVerticalSides a w h))
    (BoundaryCondition.wired (rectangleDualCornerSideColumns a w h))
    S hS (by
      intro K
      exact rectangleDualCorner_frozenPartition_le_sideColumns a w h K)

end
end PottsContinuity.PlanarMixed.Square
