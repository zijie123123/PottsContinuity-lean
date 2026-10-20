module

public import PottsContinuity.Thm3.Prop4.RawCentralRestoredComparison
public import PottsContinuity.Thm3.Prop4.RawCentralRestoredWalk

/-! # Confined full raw replay compared with the genuine stopped source law -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawConfinedReplayComparisonEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Original-edge marked connection confined to a specified vertex carrier. -/
def rectangleConfinedMarkedConnectionEvent (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (T : Set LatticeVertex) : Set (Configuration (rectangleGraph a w h)) :=
  {B | ∃ p : (openGraph (rectangleGraph a w h) B).Walk u v, ∀ x ∈ p.support, x.val ∈ T}

/-- Confinement never uses virtual boundary jumps and is increasing in
exactly the actual original open bonds. -/
theorem rectangleConfinedMarkedConnectionEvent_isUpperSet (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (T : Set LatticeVertex) :
    IsUpperSet (rectangleConfinedMarkedConnectionEvent a w h u v T) := by
  rintro B C hBC ⟨p,hp⟩
  refine ⟨p.mapLe (openGraph_mono hBC),?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

/-- For ANY confinement set, full raw replay under the wired reference is
bounded by the genuine original free law conditioned ONLY on the same raw
record. All other fresh components are integrated through the edge union. -/
theorem sourceMarkedRaw_confined_replay_probability_le_record
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A : Configuration (rectangleGraph a w h)) (θ : Parameters) (T : Set LatticeVertex) :
    (measure (rectangleGraph a w h) θ (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1)
      {B | replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
        (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∈
          rectangleConfinedMarkedConnectionEvent a w h u v T}).toReal ≤
    (((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure
      (rectangleConfinedMarkedConnectionEvent a w h u v T)).toReal := by
  have hsub : {B | replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
      (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∈
        rectangleConfinedMarkedConnectionEvent a w h u v T} ⊆
    {B | sourceMarkedRawCentralRestoration a w h u v A (sourceMarkedRawCentralRestriction a w h u v A B) ∈
      rectangleConfinedMarkedConnectionEvent a w h u v T} := by
    rintro B ⟨p,hp⟩
    exact sourceMarkedRaw_replay_walk_to_centralRestoration a w h hw hh u v hu A B T p hp
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (sourceMarkedRawCentral_restored_reference_le_record a w h hw hh u v hu A θ _
      (rectangleConfinedMarkedConnectionEvent_isUpperSet a w h u v T))

/-- A purely deterministic FULL RAW transfer of the reference event gives
the actual source conditional lower bound. No access-domain deletion remains. -/
theorem sourceMarkedRaw_confined_record_lower_of_fullReplay
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1)
    (A : Configuration (rectangleGraph a w h)) (θ : Parameters) (T : Set LatticeVertex)
    (F : Set (Configuration (rectangleGraph a w h)))
    (htransfer : ∀ B ∈ F, replayRevealedState (rectangleGraph a w h) (sourceMarkedRawReveal a w h u v A)
      (revealRecordConfiguration (sourceMarkedRawReveal a w h u v) A) B ∈
        rectangleConfinedMarkedConnectionEvent a w h u v T) :
    (measure (rectangleGraph a w h) θ (frozenBoundaryCondition (PD.FK.latticeRectangle a w h) 1) F).toReal ≤
    (((law (rectangleGraph a w h) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal a w h u v) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable a w h u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure
      (rectangleConfinedMarkedConnectionEvent a w h u v T)).toReal := by
  exact (measureReal_mono htransfer (measure_ne_top _ _)).trans
    (sourceMarkedRaw_confined_replay_probability_le_record a w h hw hh u v hu A θ T)

end
end PottsContinuity.Thm3.Prop4
