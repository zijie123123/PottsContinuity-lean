-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripBoundaryCylinderLower.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopCylinders
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

private theorem horizontalStripRectangleCylinderEvent_upper_bound
    (M n : ℕ) (F : Finset squareLattice.edgeSet) :
    IsUpperSet (horizontalStripRectangleCylinderEvent M n F) := by
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

/-- The finite all-open cylinder probability under top-only wiring is bounded
above by its probability under any boundary condition containing that wiring. -/
theorem horizontalStripRectangleProbabilityMeasure_allOpen_boundary_lower
    (q : ClusterWeight) (M n : ℕ)
    (ξ : BoundaryCondition (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)))
    (hξ : (horizontalStripTopWiredBoundary M n).partition ≤ ξ.partition)
    (F : Finset squareLattice.edgeSet) :
    ((horizontalStripRectangleProbabilityMeasure q M n
        (horizontalStripTopWiredBoundary M n) : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal ≤
      ((horizontalStripRectangleProbabilityMeasure q M n ξ : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F)).toReal := by
  rw [horizontalStripRectangleProbabilityMeasure_allOpen q M n
      (horizontalStripTopWiredBoundary M n) F,
    horizontalStripRectangleProbabilityMeasure_allOpen q M n ξ F]
  exact measure_boundary_comparison q (horizontalStripTopWiredBoundary M n) ξ hξ
    (horizontalStripRectangleCylinderEvent M n F)
    (horizontalStripRectangleCylinderEvent_upper_bound M n F)

end
end PottsContinuity.FKC.Medial
