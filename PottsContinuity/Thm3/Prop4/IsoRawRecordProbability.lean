module

public import PottsContinuity.Thm3.Prop4.MarkedBoxRawSourceIdentity
public import PottsContinuity.Thm3.RSW.FiniteConditionedDuality
public import PottsContinuity.PD.FK.BoxTranslation

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance isoRawRecordProbabilityEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- An actual graph isomorphism transports the entire raw record event,
including both the queried set and all its original recorded states. -/
theorem revealRecordEvent_iso_of_covariance {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (i : G ≃g H)
    (r : RevealMap (G := G)) (s : RevealMap (G := H))
    (hcov : ∀ B, configurationIso i (r B) = s (configurationIso i B)) (A : Configuration G) :
    (configurationIso i).symm ⁻¹' revealRecordEvent r A =
      revealRecordEvent s (configurationIso i A) := by
  ext C
  obtain ⟨B,rfl⟩ := (configurationIso i).surjective C
  simp only [Set.mem_preimage,Equiv.symm_apply_apply,revealRecordEvent,Set.mem_ofPred_eq]
  rw [← hcov B,← hcov A,← configurationIso_inter,← configurationIso_inter]
  exact and_congr (configurationIso i).injective.eq_iff.symm
    (configurationIso i).injective.eq_iff.symm

/-- Conditional free probability on the source box is exactly conditional
free probability on its coordinate-identical rectangle, given ONLY raw data. -/
theorem sourceBox_raw_conditional_probability_iso
    (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) (θ : Parameters)
    (E : Set (Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))) :
    (((law (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (markedJointBoxRawReveal n u v) A) (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (markedJointBoxRawReveal_stable n u v) A]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ A))).toMeasure
      {B | configurationIso (boxTubeRectangleIso n) B ∈ E}).toReal =
    (((law (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)) (configurationIso (boxTubeRectangleIso n) A)) (by
        rw [revealRecordEvent_eq_frozenStateEvent _ (sourceMarkedRawReveal_stable _ _ _ _ _) _]
        exact frozenStateEvent_support θ _ _ (revealRecordConfiguration _ _))).toMeasure E).toReal := by
  let i : finiteLatticeGraph (box n) ≃g rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := boxTubeRectangleIso n
  have hsupport := frozenStateEvent_support θ (BoundaryCondition.free ∅)
    (markedJointBoxRawReveal n u v A) (revealRecordConfiguration (markedJointBoxRawReveal n u v) A)
  rw [← revealRecordEvent_eq_frozenStateEvent _ (markedJointBoxRawReveal_stable n u v) A] at hsupport
  have hmap := RSW.pmf_filter_map_equiv (law (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅))
    (configurationIso i) (revealRecordEvent (markedJointBoxRawReveal n u v) A) hsupport
  have hsets := revealRecordEvent_iso_of_covariance i (markedJointBoxRawReveal n u v)
    (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) (i u) (i v))
    (markedJointBoxRawReveal_eq_source_raw n u v) A
  simp only [law_configurationIso_map,boundaryConditionIso_free_empty,hsets] at hmap
  have hprob := congrArg (fun p => (p.toMeasure E).toReal) hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hprob
  exact hprob

end
end PottsContinuity.Thm3.Prop4
