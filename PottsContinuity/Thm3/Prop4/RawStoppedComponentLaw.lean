module

public import PottsContinuity.Thm3.Prop4.RawComponentBoundaryPartition
public import PottsContinuity.Thm3.Prop4.RawMarkedStoppedLaw
public import PottsContinuity.Thm3.Prop4.RawRecordedFaceRegion
public import PottsContinuity.Thm3.Push.RectangleGraphPreconnected
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw

/-! # Exact wired component laws conditioned on the raw exploration record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
local instance rawStoppedComponentEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Restrict a source configuration to the ACTUAL unqueried edge graph of
one fixed raw source record. No queried bond is copied from the new sample. -/
def sourceMarkedRawRemainingConfiguration (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A C : Configuration (rectangleGraph a w h)) :
    Configuration (sourceMarkedRawDomain a w h u v A) :=
  (edgeRestrictionConfigurationEquiv (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)).symm
    ((configurationSplitEquiv (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A) C).1)

/-- Conditioning on the exact raw record gives its actual deleted-edge FK
law, retaining EVERY remaining component and its original induced partition. -/
theorem law_filter_sourceMarkedRawRecord_map_deleted (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) (θ : Parameters) :
    ((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).map
      (sourceMarkedRawRemainingConfiguration a w h u v A) =
      law (sourceMarkedRawDomain a w h u v A) θ (sourceMarkedRawBoundary a w h u v A) := by
  unfold sourceMarkedRawRemainingConfiguration
  let G := rectangleGraph a w h
  let R := sourceMarkedRawReveal a w h u v A
  let e := edgeRestrictionConfigurationEquiv G R
  have hdmp := law_filter_sourceMarkedRawRecord_map_remaining a w h u v θ (BoundaryCondition.free ∅) A
  have hpush := congrArg (fun p => p.map e.symm) hdmp
  rw [PMF.map_comp] at hpush
  have hrestore : (remainingLaw G θ (sourceMarkedRawBoundary a w h u v A) R).map e.symm =
      law (sourceMarkedRawDomain a w h u v A) θ (sourceMarkedRawBoundary a w h u v A) := by
    rw [← law_edgeRestriction_map]
    rw [PMF.map_comp]
    simp only [e,Function.comp_def,Equiv.symm_apply_apply]
    exact PMF.map_id _
  exact hpush.trans hrestore

end
end PottsContinuity.Thm3.Prop4
