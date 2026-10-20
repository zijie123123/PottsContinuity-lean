module

public import PottsContinuity.Thm3.Prop4.RawCentralDomain
public import PottsContinuity.Thm3.Prop4.RawStoppedComponentLaw

/-! # Exact wired law on the whole marked raw retained union -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section

/-- Integrating ALL other remaining components leaves the exact wired FK
law on the union attached to the original marked recorded class. -/
theorem sourceMarkedRaw_central_law_map (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (A : Configuration (rectangleGraph a w h)) (θ : Parameters) :
    (law (sourceMarkedRawDomain a w h u v A) θ (sourceMarkedRawBoundary a w h u v A)).map
      (embeddedConfigurationRestriction
        ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
        (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        (pocketInduced_map_le _ _)) =
    law ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A)) θ
      (BoundaryCondition.wired {x : sourceMarkedRawCentralVertices a w h u v A |
        x.val ∈ sourceMarkedRawBoundaryVertices a w h u v A}) := by
  let anchor : sourceMarkedRawCentralVertices a w h u v A :=
    ⟨u,sourceMarkedRawCentralVertices_mark a w h u v A⟩
  have hboundary : ∀ x ∈ sourceMarkedRawCentralVertices a w h u v A,
      ∀ y, y ∉ sourceMarkedRawCentralVertices a w h u v A →
      (sourceMarkedRawBoundary a w h u v A).partition.r x y →
      (sourceMarkedRawBoundary a w h u v A).partition.r x anchor.val := by
    intro x hx y hy hxy
    exact (hy (sourceMarkedRawCentralVertices_boundary_closed a w h hw hh u v hu A x hx y hxy)).elim
  exact (componentPocket_law_map (sourceMarkedRawDomain a w h u v A) θ
    (sourceMarkedRawCentralVertices a w h u v A) (sourceMarkedRawBoundary a w h u v A) anchor
    (sourceMarkedRawCentralVertices_edge_closed a w h u v A) hboundary).trans
      (law_eq_of_boundary_partition_eq θ _ _
        (sourceMarkedRawCentralVertices_partition_eq_wired a w h hw hh u v hu A))

/-- On the ORIGINAL free sample conditioned only on the raw source record,
the whole retained marked union has its exact wired FK law. -/
theorem law_filter_sourceMarkedRawRecord_map_central (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (hu : u.val.1 = a.1) (A : Configuration (rectangleGraph a w h)) (θ : Parameters) :
    ((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).map
      (fun B => embeddedConfigurationRestriction
        ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
        (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
        (pocketInduced_map_le _ _) (sourceMarkedRawRemainingConfiguration a w h u v A B)) =
    law ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A)) θ
      (BoundaryCondition.wired {x : sourceMarkedRawCentralVertices a w h u v A |
        x.val ∈ sourceMarkedRawBoundaryVertices a w h u v A}) := by
  have hdmp := law_filter_sourceMarkedRawRecord_map_deleted a w h u v A θ
  have hpush := congrArg (fun p => p.map (embeddedConfigurationRestriction
      ((sourceMarkedRawDomain a w h u v A).induce (sourceMarkedRawCentralVertices a w h u v A))
      (sourceMarkedRawDomain a w h u v A) (pocketInclusion (sourceMarkedRawCentralVertices a w h u v A))
      (pocketInduced_map_le _ _))) hdmp
  rw [PMF.map_comp] at hpush
  exact hpush.trans (sourceMarkedRaw_central_law_map a w h hw hh u v hu A θ)

end
end PottsContinuity.Thm3.Prop4
