module

public import PottsContinuity.Thm3.Prop4.RawCentralRestoration

/-! # Restored-event comparison under the unchanged raw observation -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawCentralRestoredComparisonEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Every increasing original-edge event has its restored reference probability
bounded by its genuine original probability conditioned only on the raw record. -/
theorem sourceMarkedRawCentral_restored_reference_le_record
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A : Configuration (rectangleGraph a w h)) (θ : Parameters)
    (H : Set (Configuration (rectangleGraph a w h))) (hH : IsUpperSet H) :
    (measure (rectangleGraph a w h) θ (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1)
      {B | sourceMarkedRawCentralRestoration a w h u v A (sourceMarkedRawCentralRestriction a w h u v A B) ∈ H}).toReal ≤
    (((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure H).toReal := by
  classical
  let E : Set (Configuration (sourceMarkedRawCentralGraph a w h u v A)) :=
    {K | sourceMarkedRawCentralRestoration a w h u v A K ∈ H}
  have hE : IsUpperSet E := by
    intro K L hKL hK
    exact hH (sourceMarkedRawCentralRestoration_mono a w h u v A hKL) hK
  have hcompare := sourceMarkedRaw_record_central_ge_wired_rectangle a w h hw hh u v A hu θ E hE
  let p := (law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
    (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
    (by
      rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
      exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))
  have hm : (p.toMeasure {B | sourceMarkedRawCentralRestoration a w h u v A
      (sourceMarkedRawCentralRestriction a w h u v A B) ∈ H}) ≤ p.toMeasure H := by
    apply p.toMeasure_mono MeasurableSpace.measurableSet_top
    intro B hB
    have hr := ((PMF.mem_support_filter_iff _).mp hB.2).1
    exact hH (sourceMarkedRawCentralRestoration_restriction_subset a w h u v A B hr) hB.1
  have hprob : (p.toMeasure {B | sourceMarkedRawCentralRestoration a w h u v A
      (sourceMarkedRawCentralRestriction a w h u v A B) ∈ H}).toReal ≤ (p.toMeasure H).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hm
  have heq : {B | embeddedConfigurationRestriction (sourceMarkedRawCentralGraph a w h u v A)
      (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
      (pocketInduced_map_le _ _) (sourceMarkedRawRemainingConfiguration a w h u v A B) ∈ E} =
      {B | sourceMarkedRawCentralRestoration a w h u v A (sourceMarkedRawCentralRestriction a w h u v A B) ∈ H} := by
    ext B
    exact Iff.of_eq (congrArg (fun K => sourceMarkedRawCentralRestoration a w h u v A K ∈ H)
      (sourceMarkedRawCentralRestriction_eq_remaining a w h u v A B).symm)
  have hrewrite := congrArg (fun S : Set (Configuration (rectangleGraph a w h)) => (p.toMeasure S).toReal) heq
  exact hcompare.trans (hrewrite.le.trans hprob)

end
end PottsContinuity.Thm3.Prop4
