module

public import PottsContinuity.Thm3.Push.OuterRestoredCrossing
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance outerRestoredBoundEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Quantitative actual restored-crossing bound in the OUTER stopped
remaining graph. Every geometric comparison and original-bond restoration
step is proved; the original outer physical-side wiring is retained. -/
theorem reference_crossing_le_outer_frozen_restored_crossing {V : Type*} [Finite V]
    (a : LatticeVertex) (w h n : ℕ) (hn : n ≤ h) (G : SimpleGraph V)
    (f : RectangleVertex a w h ↪ V) (hRG : (rectangleGraph a w h).map f ≤ G)
    (A : Configuration G)
    (hA : embeddedConfigurationRestriction _ _ f hRG A ∈ rectangleHorizontalCrossingEvent a w h)
    (θ : Parameters) (ξ : BoundaryCondition V)
    (hsides : ∀ u v : RectangleVertex a w h,
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) → ξ.partition.r (f u) (f v)) :
    let Rout := embeddedFilledTopReveal a w h G f hRG A
    (measure (rectangleGraph a w h) θ
      (BoundaryCondition.wired {v : RectangleVertex a w h |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(h : ℤ)})
      (DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn))).toReal ≤
    (measure (edgeRestriction G Rout) θ (frozenBoundary ξ (A ∩ Rout))
      {C | DualityExt.rectangleConfigurationRestriction (rectangle_height_subset a w n h hn)
        (embeddedConfigurationRestriction _ _ f hRG
          (restoreRemainingConfiguration _ _ ⟨A ∩ Rout,Finset.inter_subset_right⟩ C)) ∈
        rectangleHorizontalCrossingEvent a w n}).toReal := by
  have hbound := reference_event_le_outer_frozen_active_witness a w h G f hRG A hA θ ξ hsides
    (DualityExt.rectangleInnerHorizontalCrossingEvent (rectangle_height_subset a w n h hn))
  apply hbound.trans
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
  apply MeasureTheory.measure_mono
  intro C hC
  exact outer_restored_crossing_of_active_reference_witness a w h n hn G f hRG A hA C hC

end
end PottsContinuity.Push
