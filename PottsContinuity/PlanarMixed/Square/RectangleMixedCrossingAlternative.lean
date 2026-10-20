/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleMixedCrossingAlternative.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Explicit self-dual parameter for every real q>=1 via the scoped coercion.
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleMixedDuality
public import PottsContinuity.PD.Duality.CrossingDuality
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

/-- The exact mixed-boundary finite duality transports every event by the
actual primal-dual configuration equivalence. -/
theorem rectangleDoubleCollar_mixedLaw_measure_preimage
    (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (S : Set (Configuration (rectangleDualGraph a w h))) :
    measure (rectangleGraph a w h) q
        (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
          (rectangleDoubleCollarInnerTop a w h)
          (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))
        ((rectanglePrimalDualConfigurationEquiv a w h) ⁻¹' S) =
      measure (rectangleDualGraph a w h) q
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)) S := by
  have hmap := rectangleDoubleCollar_mixedDuality_law_map a w h hh q
  have hmeasure := congrArg PMF.toMeasure hmap
  rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmeasure
  change (law (rectangleGraph a w h) q
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
        (rectangleDoubleCollarInnerTop a w h)
        (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))).toMeasure
      ((rectanglePrimalDualConfigurationEquiv a w h) ⁻¹' S) = _
  calc
    (law (rectangleGraph a w h) q
        (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
          (rectangleDoubleCollarInnerTop a w h)
          (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))).toMeasure
        ((rectanglePrimalDualConfigurationEquiv a w h) ⁻¹' S) =
      Measure.map (rectanglePrimalDualConfigurationEquiv a w h)
        (law (rectangleGraph a w h) q
          (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
            (rectangleDoubleCollarInnerTop a w h)
            (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh))).toMeasure S := by
          rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
    _ = (law (rectangleDualGraph a w h) q
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h))).toMeasure S :=
      congrArg (fun μ : Measure (Configuration (rectangleDualGraph a w h)) => μ S) hmeasure

end
end PottsContinuity.PlanarMixed.Square
