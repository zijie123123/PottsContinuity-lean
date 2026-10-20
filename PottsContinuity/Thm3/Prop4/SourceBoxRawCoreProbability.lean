module

public import PottsContinuity.Thm3.Prop4.SourceBoxRawCoreGluing
public import PottsContinuity.Thm3.Prop4.IsoRawRecordProbability
public import PottsContinuity.Thm3.Prop4.BoxRectangleWiredLaw
public import PottsContinuity.Thm3.Prop4.BoxConfinedEventIso

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance sourceBoxRawCoreProbabilityEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Given the exact raw source record on the between-traces event, actual
confined marked connection dominates the wired strict-core reference event.
Every geometric and law comparison is discharged. -/
theorem sourceBox_raw_record_core_probability_le_confined
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A : Configuration (finiteLatticeGraph (box n))) (θ : Parameters)
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (hLower : ∀ z ∈ markedLowerBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ (z.val.2 : ℝ)-(t*z.val.1+b) ≤ 0)
    (hUpper : ∀ z ∈ markedUpperBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ 0 ≤ (z.val.2 : ℝ)-(t*z.val.1+b)) :
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (frozenBoundaryCondition (box n) 1)
      (inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b)).toReal ≤
    (((law (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (markedJointBoxRawReveal n u v) A) (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (markedJointBoxRawReveal_stable n u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure
      {B | ∃ p : (openGraph (finiteLatticeGraph (box n)) B).Walk u v,
        ∀ z ∈ p.support, z.val ∈ radiusTube n R u.val v.val}).toReal := by
  classical
  let i : finiteLatticeGraph (box n) ≃g rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := boxTubeRectangleIso n
  let F : Set (Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))) :=
    (configurationIso i).symm ⁻¹' inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b
  let H := rectangleConfinedMarkedConnectionEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (i u) (i v)
    (↑(radiusTube n R u.val v.val) : Set LatticeVertex)
  have htransfer : ∀ B ∈ F, replayRevealedState (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
      (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (i u) (i v) (configurationIso i A))
      (revealRecordConfiguration (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (i u) (i v))
        (configurationIso i A)) B ∈ H := by
    intro B hB
    obtain ⟨B,rfl⟩ := (configurationIso i).surjective B
    have hcore : B ∈ inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b := by
      simpa only [F,Set.mem_preimage,Equiv.symm_apply_apply] using hB
    exact sourceBox_raw_replay_strict_core_gluing n hn R hR u v hu hv t b ht hut hvt A B hA hLower hUpper hcore
  have hprob := sourceMarkedRaw_confined_record_lower_of_fullReplay (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (by omega) (by omega) (i u) (i v) hu (configurationIso i A) θ _ F htransfer
  have href := sourceBox_wired_probability_iso n θ F
  have hF : {B : Configuration (finiteLatticeGraph (box n)) | configurationIso i B ∈ F} =
      inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b := by
    ext B
    exact Iff.of_eq (congrArg (fun C => C ∈ inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b)
      ((configurationIso i).symm_apply_apply B))
  have href' := congrArg (fun E : Set (Configuration (finiteLatticeGraph (box n))) =>
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (frozenBoundaryCondition (box n) 1) E).toReal) hF
  have hcond := sourceBox_raw_conditional_probability_iso n u v A θ H
  have hH : {B : Configuration (finiteLatticeGraph (box n)) | configurationIso (boxTubeRectangleIso n) B ∈ H} =
      {B | ∃ p : (openGraph (finiteLatticeGraph (box n)) B).Walk u v,
        ∀ z ∈ p.support, z.val ∈ radiusTube n R u.val v.val} :=
    sourceBox_confined_event_iso n u v ↑(radiusTube n R u.val v.val)
  rw [hH] at hcond
  exact (href.trans href').symm.le.trans (hprob.trans_eq hcond.symm)

end
end PottsContinuity.Thm3.Prop4
