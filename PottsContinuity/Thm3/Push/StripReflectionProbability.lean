module

public import PottsContinuity.Thm3.Push.StripReflectionWindowStates

@[expose] public section

namespace PottsContinuity.Push
open PD.FK MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Every actual strip event has equal finite-window probability to its
horizontal reflection, on the literal closed extension. -/
theorem stripWindowEventProbability_reflection (θ : Parameters) (n m : ℕ)
    (E : Set (RSW.StripConfiguration n)) :
    RSW.stripWindowEventProbability θ n m E =
      RSW.stripWindowEventProbability θ n m ((stripHorizontalReflection n) ⁻¹' E) := by
  let A := {C | RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) ∈ E}
  have hmap := congrArg (fun ρ => (ρ : PMF (Configuration
    (PottsContinuity.squareLattice.induce (RSW.stripWindow n m : Set (ℤ × ℤ))))).toMeasure A)
      (stripWindow_law_reflection_map θ n m 0)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hmap
  have hpre : (configurationIso (stripWindowHorizontalReflectionIso n m)) ⁻¹' A =
      {C | RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m C) ∈
        (stripHorizontalReflection n) ⁻¹' E} := by
    ext C
    change RSW.stripPlaneRestriction n (RSW.stripWindowPlaneConfiguration n m
      (configurationIso (stripWindowHorizontalReflectionIso n m) C)) ∈ E ↔ _
    rw [stripWindow_extension_reflection]
    rfl
  rw [hpre] at hmap
  exact (congrArg ENNReal.toReal hmap).symm

/-- The genuine top-wired strip limit is horizontally reflection invariant
on every clopen event, for every interior edge parameter and real q at least one. -/
theorem strip_limit_clopen_reflection (θ : Parameters) (n : ℕ)
    (μ : Measure (RSW.StripConfiguration n)) (hμ : RSW.IsTopWiredStripLimit θ n 0 μ)
    (E : Set (RSW.StripConfiguration n)) (hE : IsClopen E) :
    μ.real E = μ.real ((stripHorizontalReflection n) ⁻¹' E) := by
  have h₁ := RSW.stripWindowEventProbability_tendsto θ n μ hμ E hE
  have h₂ := RSW.stripWindowEventProbability_tendsto θ n μ hμ
    ((stripHorizontalReflection n) ⁻¹' E)
    (hE.preimage (stripHorizontalReflection_continuous n))
  have heq : (fun m => RSW.stripWindowEventProbability θ n m E) =
      (fun m => RSW.stripWindowEventProbability θ n m ((stripHorizontalReflection n) ⁻¹' E)) := by
    funext m
    exact stripWindowEventProbability_reflection θ n m E
  rw [heq] at h₁
  exact tendsto_nhds_unique h₁ h₂

end
end PottsContinuity.Push
