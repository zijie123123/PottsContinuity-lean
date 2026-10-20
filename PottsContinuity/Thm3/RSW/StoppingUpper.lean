module

public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance stoppingUpperEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Uniform conditional upper bounds on all attained stopping records average
to the same unconditional upper bound. Only realized records are indexed. -/
theorem stopped_event_upper_of_record_bounds
    (θ : Parameters) (ξ : BoundaryCondition V) (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (A : Set (Configuration G)) (c : ℝ)
    (hrecord : ∀ C₀ : Configuration G, (((law G θ ξ).filter (revealRecordEvent reveal C₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
          exact frozenStateEvent_support θ ξ (reveal C₀)
            (revealRecordConfiguration reveal C₀))).toMeasure A).toReal ≤ c) :
    (measure G θ ξ A).toReal ≤ c := by
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
  have hconditional : ∀ b,
      ((p.filter {C | f C = b} (hf b)).toMeasure A).toReal ≤ c := by
    intro b
    obtain ⟨C₀, hC₀⟩ := b.property
    have heq : f C₀ = b := Subtype.ext hC₀
    have hset : {C | f C = b} = revealRecordEvent reveal C₀ := by
      rw [← heq]
      exact stoppingObservationMap_fiber reveal C₀
    simpa only [hset] using hrecord C₀
  have h := PD.RCInfinite.pmf_joint_le_of_fiber_le p f hf A Set.univ c hconditional
  change (p.toMeasure A).toReal ≤ c
  simpa only [Set.preimage_univ, Set.inter_univ, measure_univ, ENNReal.toReal_one,
    mul_one] using h

end
end PottsContinuity.RSW
