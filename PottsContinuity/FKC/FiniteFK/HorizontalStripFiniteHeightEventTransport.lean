-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripFiniteHeightEventTransport.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightDualAlternative
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightClopenApproximation
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open MeasureTheory

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC.FiniteFK
noncomputable section

local instance heightTransportEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance heightTransportEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance heightTransportConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripCutRectangle N n)) := Fintype.ofFinite _

/-- Restricting the literal closed extension recovers the original finite
configuration on every actual rectangle edge. -/
theorem horizontalStripRectangleRestriction_planeExtension_eq
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n)) :
    horizontalStripRectangleRestriction N n (horizontalStripRectanglePlaneExtension N n A) = A := by
  ext e
  simp [horizontalStripRectangleRestriction,
    horizontalStripRectanglePlaneExtension_mem_originalEdge]

/-- The finite center-to-top event is exactly the clopen finite-height event
when evaluated on the literal whole-plane extension of the same configuration. -/
theorem rectangleCenterTopConnectionEvent_iff_heightFiniteRectangleEvent_extension
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n)) :
    A ∈ rectangleCenterTopConnectionEvent N n ↔
      horizontalStripRectanglePlaneExtension N n A ∈
        horizontalStripHeightFiniteRectangleEvent N n := by
  rw [horizontalStripHeightFiniteRectangleEvent]
  simp only [Set.mem_ofPred_eq]
  rw [horizontalStripRectangleRestriction_planeExtension_eq]
  rfl

/-- Under the genuine finite top-wired FK law, the center-to-top event has
probability at most the original whole-plane height-sublevel mass under the
same finite law extended by closed edges. -/
theorem rectangleCenterTopConnectionEvent_probability_le_heightLE
    (q : ClusterWeight) (N n : ℕ) :
    (measure (horizontalStripCutRectangle N n) q (horizontalStripTopWiredBoundary N n)
      (rectangleCenterTopConnectionEvent N n)).toReal ≤
    ((horizontalStripRectangleProbabilityMeasure q N n
      (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
      {ω | horizontalStripHeight n ω 0 ≤ n}).toReal := by
  have hpre : {A : Configuration (horizontalStripCutRectangle N n) |
      horizontalStripRectanglePlaneExtension N n A ∈
        horizontalStripHeightFiniteRectangleEvent N n} =
      rectangleCenterTopConnectionEvent N n := by
    ext A
    exact (rectangleCenterTopConnectionEvent_iff_heightFiniteRectangleEvent_extension N n A).symm
  have happly := horizontalStripRectangleProbabilityMeasure_apply_preimage q N n
      (horizontalStripTopWiredBoundary N n)
      (horizontalStripHeightFiniteRectangleEvent N n)
      (isClopen_horizontalStripHeightFiniteRectangleEvent N n).isOpen.measurableSet
  have hsub : horizontalStripHeightFiniteRectangleEvent N n ⊆
      {ω | horizontalStripHeight n ω 0 ≤ n} :=
    horizontalStripHeightFiniteRectangleEvent_subset_heightLE N n
  calc
    (measure (horizontalStripCutRectangle N n) q (horizontalStripTopWiredBoundary N n)
        (rectangleCenterTopConnectionEvent N n)).toReal =
      ((horizontalStripRectangleProbabilityMeasure q N n
        (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
        (horizontalStripHeightFiniteRectangleEvent N n)).toReal := by
          rw [happly, hpre]
    _ ≤ ((horizontalStripRectangleProbabilityMeasure q N n
        (horizontalStripTopWiredBoundary N n) : Measure LatticeConfiguration)
        {ω | horizontalStripHeight n ω 0 ≤ n}).toReal := by
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

end
end PottsContinuity.FKC.Medial
