-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripRectangleLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.BoxCompactness
public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

attribute [local instance] PottsContinuity.FKC.FiniteFK.configurationMeasurableSpace

/-- The actual finite FK law on the strip rectangle, extended by closed edges
outside its original finite edge set. -/
def horizontalStripRectangleLaw (q : PottsContinuity.FKC.ClusterWeight) (M n : ℕ)
    (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition
      (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n))) : PMF LatticeConfiguration :=
  (PottsContinuity.FKC.FiniteFK.law (horizontalStripCutRectangle M n) q ξ).map
    (horizontalStripRectanglePlaneExtension M n)

/-- The finite FK strip-rectangle law viewed as a probability measure on the
natural whole-plane product carrier. -/
def horizontalStripRectangleProbabilityMeasure (q : PottsContinuity.FKC.ClusterWeight)
    (M n : ℕ) (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition
      (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n))) : ProbabilityMeasure LatticeConfiguration :=
  ⟨(horizontalStripRectangleLaw q M n ξ).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

theorem horizontalStripRectangleProbabilityMeasure_apply_preimage
    (q : PottsContinuity.FKC.ClusterWeight) (M n : ℕ)
    (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition
      (RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)))
    (s : Set LatticeConfiguration) (hs : MeasurableSet s) :
    (horizontalStripRectangleProbabilityMeasure q M n ξ : Measure LatticeConfiguration) s =
      PottsContinuity.FKC.FiniteFK.measure (horizontalStripCutRectangle M n) q ξ
        {A | horizontalStripRectanglePlaneExtension M n A ∈ s} := by
  change ((PottsContinuity.FKC.FiniteFK.law (horizontalStripCutRectangle M n) q ξ).map
    (horizontalStripRectanglePlaneExtension M n)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

end
end PottsContinuity.FKC.Medial

