-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripOriginSmallestScale.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.StripSmallestScale
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowTranslation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory
noncomputable section

/-- The literal smallest-scale open connection is a subevent of the actual
origin-based local wired connection event at radius and height one. -/
theorem stripSmallOriginTopConnectionEvent_subset_originLocal :
    stripSmallOriginTopConnectionEvent ⊆ horizontalStripOriginLocalConnectionEvent 1 1 := by
  intro A hA
  refine ⟨stripSmallTopVertex, ?_, ?_⟩
  · change stripSmallTopVertex.val ∈
      rectangleLeftSide (-1, 0) 2 1 ∪ rectangleRightSide (-1, 0) 2 1 ∪
        rectangleTopSide (-1, 0) 2 1
    simp [stripSmallTopVertex, rectangleTopSide, Finset.mem_filter,
      mem_latticeRectangle]
  · change ActualConnected stripSmallGraph A stripSmallBottomVertex stripSmallTopVertex at hA
    simpa [stripSmallGraph, stripSmallBottomVertex,
      horizontalStripOriginLocalRoot] using hA

/-- The true origin-based wired local connection probability has the
smallest-scale lower bounds supplied by finite energy. -/
theorem horizontalStripOriginLocalConnection_probability_gt_constants
    (q : ClusterWeight) :
    (1 / 3 : ℝ) <
        (measure (rectangleGraph (-(1 : ℤ), 0) (2 * 1) 1) q
          (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet 1 1))
          (horizontalStripOriginLocalConnectionEvent 1 1)).toReal ∧
      (1 / 5 : ℝ) <
        (measure (rectangleGraph (-(1 : ℤ), 0) (2 * 1) 1) q
          (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet 1 1))
          (horizontalStripOriginLocalConnectionEvent 1 1)).toReal := by
  let ξ := BoundaryCondition.wired (horizontalStripOriginLocalWiredSet 1 1)
  have hsubset : stripSmallOriginTopConnectionEvent ⊆
      horizontalStripOriginLocalConnectionEvent 1 1 :=
    stripSmallOriginTopConnectionEvent_subset_originLocal
  have hmono :
      measure stripSmallGraph q ξ stripSmallOriginTopConnectionEvent ≤
        measure stripSmallGraph q ξ (horizontalStripOriginLocalConnectionEvent 1 1) :=
    measure_mono hsubset
  have hreal := ENNReal.toReal_mono
    (measure_ne_top (measure stripSmallGraph q ξ)
      (horizontalStripOriginLocalConnectionEvent 1 1)) hmono
  have hsmall := stripSmallOriginTopConnection_probability_gt_constants q ξ
  constructor
  · change (1 / 3 : ℝ) <
        (measure stripSmallGraph q ξ
          (horizontalStripOriginLocalConnectionEvent 1 1)).toReal
    exact hsmall.1.trans_le hreal
  · change (1 / 5 : ℝ) <
        (measure stripSmallGraph q ξ
          (horizontalStripOriginLocalConnectionEvent 1 1)).toReal
    exact hsmall.2.trans_le hreal

end
end PottsContinuity.FKC.FiniteFK
