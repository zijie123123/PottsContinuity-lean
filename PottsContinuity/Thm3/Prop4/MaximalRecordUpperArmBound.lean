module

public import PottsContinuity.Thm3.Prop4.MaximalTraceUpperArm
public import PottsContinuity.Thm3.Prop4.StoppedJointLowerBound

/-!
# The maximal-excursion upper-arm bound on selected actual source records

The complete observation selects the source event. A columnwise lower
reveal, the unchanged maximal Euclidean event and exact stopping stability
suffice for the joint upper-arm estimate. The actual prescribed-path selector
and its deterministic reveal properties remain explicit geometric inputs.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance maximalRecordUpperEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- The corrected polynomial upper-arm cost on the exact original source
observations, conditional only on touch and deterministic selected-path data. -/
theorem maximal_record_upper_arm_joint_lower_of_touch_and_column_reveal
    (q : Set.Ici (1 : ℝ)) {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v z : LatticeVertex)
    (huB : u ∈ box n) (hvB : v ∈ box n) (hzB : z ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (trace : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) → Finset LatticeVertex)
    (reveal : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) →
      Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (T : Set (RSW.StoppingObservationRange reveal))
    (htrace : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → ∀ w ∈ trace C₀, w ∈ box n)
    (huT : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → u ∈ trace C₀)
    (hvT : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → v ∈ trace C₀)
    (hmax : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T →
      C₀ ∈ maximalTubeExcursionEvent n ε u v trace z)
    (hR : ∀ C₀, RSW.stoppingObservationMap reveal C₀ ∈ T → ∀ e ∈ reveal C₀,
      (∃ w ∈ trace C₀,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace C₀,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) *
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        ((RSW.stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
            ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box]; exact hzB⟩)
          (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
          (fun _ => True) ∩ ((RSW.stoppingObservationMap reveal) ⁻¹' T))).toReal := by
  apply stopped_event_joint_lower_of_original_record_bounds
    (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (RSW.selfDualParameters q)
    (BoundaryCondition.free ∅) reveal hstable _ T _
  intro C₀ hC₀
  erw [stable_record_original_event_probability_eq_reconstructed
    (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (RSW.selfDualParameters q)
    (BoundaryCondition.free ∅) reveal hstable C₀,
    stableRecordRemainingLaw_eq_frozenFiberLaw
    (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (RSW.selfDualParameters q)
    (BoundaryCondition.free ∅) reveal hstable C₀]
  exact maximal_trace_upper_arm_lower_of_touch_and_column_reveal q hn ε u v huB hvB huX hvX
    trace C₀ (htrace C₀ hC₀) (huT C₀ hC₀) (hvT C₀ hC₀) z (hmax C₀ hC₀)
    (reveal C₀) (Exploration.revealRecordConfiguration reveal C₀) (hR C₀ hC₀) hTouch

end
end PottsContinuity.Thm3.Prop4
