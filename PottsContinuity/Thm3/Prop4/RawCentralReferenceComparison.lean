module

public import PottsContinuity.Thm3.Prop4.ComponentReferenceBoundary
public import PottsContinuity.Thm3.Prop4.RawCentralLaw

/-! # Wired rectangle comparison for the whole marked raw union -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawCentralReferenceEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The whole retained marked union's wired law dominates the wired rectangle
restriction. Every reference exterior-state partition comparison is proved;
there is no extra reference partition or probability premise. -/
theorem sourceMarkedRaw_central_wired_reference_probability_le
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (hu : u.val.1 = a.1) (θ : Parameters)
    (E : Set (Configuration ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))))
    (hE : IsUpperSet E) :
    (measure (rectangleGraph a w h) θ (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1)
      {B | embeddedConfigurationRestriction ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
        (rectangleGraph a w h) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        ((pocketInduced_map_le (sourceMarkedRawDomain a w h u v A) (sourceMarkedRawCentralVertices a w h u v A)).trans
          (edgeRestriction_le (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A))) B ∈ E}).toReal ≤
      (measure ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A)) θ
        (BoundaryCondition.wired {x : (sourceMarkedRawCentralVertices a w h u v A) | x.val ∈ sourceMarkedRawBoundaryVertices a w h u v A}) E).toReal := by
  apply embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
  · exact hE
  · intro K
    apply edgeClosed_remaining_reference_partition_le (rectangleGraph a w h)
      (sourceMarkedRawReveal a w h u v A) (sourceMarkedRawCentralVertices a w h u v A)
      (sourceMarkedRawCentralVertices_edge_closed a w h u v A)
      (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1)
      ⟨u,sourceMarkedRawCentralVertices_mark a w h u v A⟩
      (sourceMarkedRawBoundaryVertices_of_rectangle_side a w h hw hh u v u A (Or.inl hu))
    · intro x y hxy
      change (BoundaryCondition.wired (frozenVertexBoundary (PD.FK.latticeRectangle a w h))).partition.r x y at hxy
      rcases (BoundaryCondition.wired_rel _ x y).mp hxy with h | ⟨hx,hy⟩
      · exact Or.inl h
      · right
        exact ⟨frozenVertexBoundary_subset_sourceMarkedRawBoundaryVertices a w h hw hh u v A hx,
          frozenVertexBoundary_subset_sourceMarkedRawBoundaryVertices a w h hw hh u v A hy⟩

/-- Conditioned on the literal source raw record, its marked-union event is at
least as likely as the same marked-union restriction under the wired rectangle.
All other remaining components are integrated, not added to the record. -/
theorem sourceMarkedRaw_record_central_ge_wired_rectangle
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (hu : u.val.1 = a.1) (θ : Parameters)
    (E : Set (Configuration ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))))
    (hE : IsUpperSet E) :
    (measure (rectangleGraph a w h) θ (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1)
      {B | embeddedConfigurationRestriction ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
        (rectangleGraph a w h) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        ((pocketInduced_map_le (sourceMarkedRawDomain a w h u v A) (sourceMarkedRawCentralVertices a w h u v A)).trans
          (edgeRestriction_le (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A))) B ∈ E}).toReal ≤
    (((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure
      {B | embeddedConfigurationRestriction ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
        (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        (pocketInduced_map_le (sourceMarkedRawDomain a w h u v A) (sourceMarkedRawCentralVertices a w h u v A))
        (sourceMarkedRawRemainingConfiguration a w h u v A B) ∈ E}).toReal := by
  have hlaw := law_filter_sourceMarkedRawRecord_map_central a w h hw hh u v hu A θ
  have hm := congrArg (fun p => (p.toMeasure E).toReal) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ (fun _ _ => MeasurableSpace.measurableSet_top)
    MeasurableSpace.measurableSet_top] at hm
  exact (sourceMarkedRaw_central_wired_reference_probability_le a w h hw hh u v A hu θ E hE).trans_eq hm.symm

end
end PottsContinuity.Thm3.Prop4
