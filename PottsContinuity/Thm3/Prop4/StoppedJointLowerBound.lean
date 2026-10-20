module

public import PottsContinuity.Thm3.Prop4.StableRecordOriginalLaw
public import PottsContinuity.Thm3.RSW.StoppingAverage

/-!
# Selected complete records retain their source event in lower-bound averaging

The original conditional law is supported on its exact complete record.
Thus averaging lower bounds retains the joint event with the selected
observation, which is needed before the source star surgery.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance stoppedJointLowerEdgeEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- Conditional bounds on selected actual records integrate to their joint
source-event bound, with the exact complete observation retained. -/
theorem stopped_event_joint_lower_of_original_record_bounds
    (V : Finset LatticeVertex) (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex))))
    (T : Set (RSW.StoppingObservationRange reveal)) (c : ℝ)
    (hrecord : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T →
      c ≤ ((stableRecordOriginalLaw V θ ξ reveal hstable C₀).toMeasure E).toReal) :
    c*(measure _ θ ξ ((RSW.stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
      (measure _ θ ξ (E ∩ ((RSW.stoppingObservationMap reveal) ⁻¹' T))).toReal := by
  apply RSW.stopped_event_lower_of_record_bounds θ ξ reveal hstable _ T c
  intro C₀ hC₀
  let p := stableRecordOriginalLaw V θ ξ reveal hstable C₀
  have hsource : p.support ⊆ ((RSW.stoppingObservationMap reveal) ⁻¹' T) := by
    intro C hC
    have hRec : C ∈ Exploration.revealRecordEvent reveal C₀ :=
      ((PMF.mem_support_filter_iff _).mp hC).1
    have hSame : RSW.stoppingObservationMap reveal C = RSW.stoppingObservationMap reveal C₀ := by
      change C ∈ {D | RSW.stoppingObservationMap reveal D = RSW.stoppingObservationMap reveal C₀}
      rw [RSW.stoppingObservationMap_fiber]
      exact hRec
    change RSW.stoppingObservationMap reveal C ∈ T
    rw [hSame]
    exact hC₀
  have hEq : (E ∩ ((RSW.stoppingObservationMap reveal) ⁻¹' T)) ∩ p.support = E ∩ p.support := by
    ext C
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · exact fun h => ⟨⟨h.1,hsource h.2⟩,h.2⟩
  have hprob := p.toMeasure_apply_eq_of_inter_support_eq MeasurableSpace.measurableSet_top
    MeasurableSpace.measurableSet_top hEq
  change c ≤ (p.toMeasure _).toReal
  rw [hprob]
  exact hrecord C₀ hC₀

end
end PottsContinuity.Thm3.Prop4
