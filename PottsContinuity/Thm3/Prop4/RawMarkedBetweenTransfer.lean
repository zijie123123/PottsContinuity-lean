module

public import PottsContinuity.Thm3.Prop4.RawMarkedMiddleLaw
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PD.FK.FrozenBridge
public import PottsContinuity.Thm3.Prop4.SourceMiddleDomain
public import PottsContinuity.Thm3.Prop4.LowerTraceHull
public import PottsContinuity.PlanarTopology.RectangleBoundaryArcIntersection
public import PottsContinuity.PlanarTopology.KSTCurveIntersection
public import PottsContinuity.Thm3.Prop4.ComponentPocketMarginal
public import PottsContinuity.PD.FK.EmbeddedBoundaryUpper
public import PottsContinuity.Thm3.Prop4.ObservedBetweenTraceEvent

/-! # Averaging actual raw middle transfer over the source between event -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawMarkedBetweenTransferEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- The source between event is determined by the literal raw observation,
including its actual original connection, with no separate path premise. -/
theorem markedJointRaw_between_event_eq_observation_preimage
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ)) :
    betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v) =
      (RSW.stoppingObservationMap (markedJointBoxRawReveal n u v)) ⁻¹'
        ((RSW.stoppingObservationMap (markedJointBoxRawReveal n u v)) ''
          betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v)) := by
  apply betweenTubeTraceEvent_eq_observation_preimage
  · exact markedJointBoxRawReveal_observes_traces n u v
  · intro A hA
    obtain ⟨pU,pL,hpU,hpL⟩ := markedJointBoxRawReveal_recorded_paths_of_marked_connection n hn u v hu hv A hA.1
    exact ⟨pU⟩

end
end PottsContinuity.Thm3.Prop4
