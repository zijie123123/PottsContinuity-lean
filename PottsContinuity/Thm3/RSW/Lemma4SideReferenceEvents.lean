module

public import PottsContinuity.Thm3.RSW.Lemma4SideBandErasure
public import PottsContinuity.Thm3.RSW.ErasureRemainingCommute

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The actual source dual band crossing under the side reference law:
include its sampled residual bonds into the original carrier and close the
unsampled bonds. This definition applies to every sample and every scale. -/
def lemma4SideReferenceEvent (n : ℕ) (i : Fin 2) :
    Set (Configuration (lemma4SideResidualGraph n (lemma4SideSign i))) :=
  {A | (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n)
    (inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i)) A)).val ∈
      lemma4DualBandEvent n i}

/-- The reference crossing is decreasing in its actual sampled bonds. -/
theorem lemma4SideReferenceEvent_isLowerSet (n : ℕ) (i : Fin 2) :
    IsLowerSet (lemma4SideReferenceEvent n i) := by
  intro A B hAB hB
  apply lemma4DualBandEvent_isLowerSet n i ?_ hB
  exact (edgeRestrictionConfigurationOrderIso (lemma4AmbientGraph n) (lemma4MiddleReveal n)).monotone
    (inducedConfigurationExtension_monotone (lemma4SideVertices n (lemma4SideSign i)) hAB)

/-- The original source dual band and the restricted side-reference event
are exactly the same event on every residual sample. No state transfer or
geometry premise remains. -/
theorem lemma4SideReferenceEvent_restriction_iff (n : ℕ) (i : Fin 2)
    (A : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n))) :
    (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val ∈
      lemma4DualBandEvent n i ↔
    inducedConfigurationRestriction (lemma4SideVertices n (lemma4SideSign i)) A ∈
      lemma4SideReferenceEvent n i := by
  have h := lemma4DualBandEvent_side_erasure_iff n i
    (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val
  rw [← edgeRestrictionConfigurationEquiv_inducedErasure] at h
  exact h

end
end PottsContinuity.RSW
