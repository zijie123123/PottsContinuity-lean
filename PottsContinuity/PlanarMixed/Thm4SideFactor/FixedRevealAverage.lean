module

public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open MeasureTheory PD.FK Exploration RSW
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance fixedAverageEdgeEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

theorem fixedReveal_joint_lower_of_remaining_bounds
    (θ : Parameters) (ξ : BoundaryCondition V) (R : Configuration G)
    (E F : Set (Configuration G)) (c : ℝ)
    (hinvariant : ∀ A B : Configuration G, B ∩ R = A ∩ R → (A ∈ E ↔ B ∈ E))
    (hbound : ∀ A ∈ E,
      c ≤ ((remainingLaw G θ (frozenBoundary ξ (A ∩ R)) R).toMeasure
        {D | D.val ∪ (A ∩ R) ∈ F}).toReal) :
    c * (measure G θ ξ E).toReal ≤ (measure G θ ξ (E ∩ F)).toReal := by
  classical
  let reveal : RevealMap (G := G) := fun _ => R
  let T : Set (StoppingObservationRange reveal) := stoppingObservationMap reveal '' E
  have hstable : ∀ A B : Configuration G,
      B ∩ reveal A = A ∩ reveal A → reveal B = reveal A := fun _ _ _ => rfl
  have hpre : (stoppingObservationMap reveal) ⁻¹' T = E := by
    ext A
    constructor
    · rintro ⟨B,hB,hBA⟩
      have hf : A ∈ revealRecordEvent reveal B := by
        rw [← stoppingObservationMap_fiber reveal B]
        exact hBA.symm
      exact (hinvariant B A hf.2).mp hB
    · intro hA
      exact ⟨A,hA,rfl⟩
  have hstop := stopped_event_lower_of_record_bounds θ ξ reveal hstable (E ∩ F) T c (by
    intro A hA
    have hAE : A ∈ E := by
      have : A ∈ (stoppingObservationMap reveal) ⁻¹' T := hA
      rwa [hpre] at this
    apply stopped_connection_lower_of_remaining_bound θ ξ reveal hstable A
      {D | D.val ∪ (A ∩ R) ∈ F} (E ∩ F) c
    · exact hbound A hAE
    · intro B hB hD
      refine ⟨(hinvariant A B hB.2).mp hAE,?_⟩
      have hrestore := (configurationSplitEquiv G R).symm_apply_apply B
      have hstate : (configurationSplitEquiv G R B).2.val = A ∩ R := by
        change B ∩ R = A ∩ R
        exact hB.2
      change (configurationSplitEquiv G R B).1.val ∪ (A ∩ R) ∈ F at hD
      rw [← hstate] at hD
      exact hrestore ▸ hD)
  rwa [hpre] at hstop

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
