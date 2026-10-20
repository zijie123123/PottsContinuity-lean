module

public import PottsContinuity.Thm3.RSW.StoppingUpper

/-! # Joint upper bounds for events measurable in a complete stopping record -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance stoppingJointUpperEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- A uniform conditional upper bound can be multiplied by the probability
of any event determined by the complete stable observation. -/
theorem stopped_event_inter_upper_of_record_bounds
    (θ : Parameters) (ξ : BoundaryCondition V) (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (A B : Set (Configuration G)) (c : ℝ)
    (hB : ∀ C₀ C, C ∈ revealRecordEvent reveal C₀ → (C ∈ B ↔ C₀ ∈ B))
    (hrecord : ∀ C₀ : Configuration G, (((law G θ ξ).filter (revealRecordEvent reveal C₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
          exact frozenStateEvent_support θ ξ (reveal C₀)
            (revealRecordConfiguration reveal C₀))).toMeasure A).toReal ≤ c) :
    (measure G θ ξ (A ∩ B)).toReal ≤ c * (measure G θ ξ B).toReal := by
  classical
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let : Fintype (StoppingObservationRange reveal) := Fintype.ofFinite _
  let p := law G θ ξ
  let f := stoppingObservationMap reveal
  have hf : ∀ b, ∃ C ∈ {C | f C = b}, C ∈ p.support := by
    intro b
    obtain ⟨C,hC⟩ := b.property
    exact ⟨C, Subtype.ext hC, (law_pos G θ ξ C).ne'⟩
  have hconditional : ∀ b,
      ((p.filter {C | f C = b} (hf b)).toMeasure A).toReal ≤ c := by
    intro b
    obtain ⟨C₀,hC₀⟩ := b.property
    have heq : f C₀ = b := Subtype.ext hC₀
    have hset : {C | f C = b} = revealRecordEvent reveal C₀ := by
      rw [← heq]
      exact stoppingObservationMap_fiber reveal C₀
    simpa only [hset] using hrecord C₀
  let T := f '' B
  have hpre : f ⁻¹' T = B := by
    ext C
    constructor
    · rintro ⟨C₀,hC₀,hfC⟩
      have hrec : C ∈ revealRecordEvent reveal C₀ := by
        rw [← stoppingObservationMap_fiber reveal C₀]
        exact hfC.symm
      exact (hB C₀ C hrec).mpr hC₀
    · intro hC
      exact ⟨C,hC,rfl⟩
  have h := PD.RCInfinite.pmf_joint_le_of_fiber_le p f hf A T c hconditional
  rw [hpre] at h
  exact h

end
end PottsContinuity.RSW
