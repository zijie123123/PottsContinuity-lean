module

public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
open scoped BigOperators
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance stoppingJointEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- Disintegration retains the selected observation event in the target. -/
theorem stopped_joint_event_lower_of_record_bounds
    (θ : Parameters) (ξ : BoundaryCondition V) (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (A : Set (Configuration G)) (T : Set (StoppingObservationRange reveal)) (c : ℝ)
    (hrecord : ∀ C₀ : Configuration G, stoppingObservationMap reveal C₀ ∈ T →
      c ≤ (((law G θ ξ).filter (revealRecordEvent reveal C₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
          exact frozenStateEvent_support θ ξ (reveal C₀)
            (revealRecordConfiguration reveal C₀))).toMeasure A).toReal) :
    c * (measure G θ ξ ((stoppingObservationMap reveal) ⁻¹' T)).toReal ≤
      (measure G θ ξ (A ∩ (stoppingObservationMap reveal) ⁻¹' T)).toReal := by
  classical
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let : Fintype (StoppingObservationRange reveal) := Fintype.ofFinite _
  let p := law G θ ξ
  let f := stoppingObservationMap reveal
  have hf : ∀ b, ∃ C ∈ {C | f C = b}, C ∈ p.support := by
    intro b
    obtain ⟨C, hC⟩ := b.property
    refine ⟨C, Subtype.ext hC, ?_⟩
    exact (law_pos G θ ξ C).ne'
  have hconditional : ∀ b ∈ T,
      c ≤ ((p.filter {C | f C = b} (hf b)).toMeasure A).toReal := by
    intro b hb
    obtain ⟨C₀, hC₀⟩ := b.property
    have heq : f C₀ = b := Subtype.ext hC₀
    have hselected : stoppingObservationMap reveal C₀ ∈ T := by
      change f C₀ ∈ T
      rw [heq]
      exact hb
    have h := hrecord C₀ hselected
    have hset : {C | f C = b} = revealRecordEvent reveal C₀ := by
      rw [← heq]
      exact stoppingObservationMap_fiber reveal C₀
    simpa only [hset] using h
  have hmass : (p.toMeasure (f ⁻¹' T)).toReal =
      ∑ b, ((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0) := by
    rw [PD.RCInfinite.pmf_measureReal_eq_expectation]
    have hmap := FiniteProbability.expectation_map p f (T.indicator (fun _ => (1 : ℝ)))
    simpa [FiniteProbability.expectation, Set.indicator] using hmap.symm
  calc
    c * (p.toMeasure (f ⁻¹' T)).toReal =
        ∑ b, c * (((p.map f) b).toReal * (if b ∈ T then (1 : ℝ) else 0)) := by
      rw [hmass, Finset.mul_sum]
    _ ≤ ∑ b, ((p.map f) b).toReal *
        (if b ∈ T then ((p.filter {C | f C = b} (hf b)).toMeasure A).toReal else 0) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b ∈ T
      · simp only [hb, ite_true, mul_one]
        calc
          c * ((p.map f) b).toReal = ((p.map f) b).toReal * c := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hconditional b hb) ENNReal.toReal_nonneg
      · simp only [hb, ite_false, mul_zero, le_refl]
    _ = (p.toMeasure (A ∩ f ⁻¹' T)).toReal :=
      (PD.RCInfinite.pmf_joint_fiber_sum p f hf A T).symm

end
end PottsContinuity.RSW
