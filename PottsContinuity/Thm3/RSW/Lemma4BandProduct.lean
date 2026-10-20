module

public import PottsContinuity.Thm3.RSW.Lemma4SideReferenceEvents

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The actual finite side-reference probability on the residual original
bonds, with exactly the base row wired. -/
def lemma4SideReferenceProbability (θ : Parameters) (n : ℕ) (i : Fin 2) : ℝ :=
  (measure (lemma4SideResidualGraph n (lemma4SideSign i)) θ
    (BoundaryCondition.wired (lemma4SideBase n (lemma4SideSign i)))
    (lemma4SideReferenceEvent n i)).toReal

theorem lemma4SideReferenceProbability_nonneg (θ : Parameters) (n : ℕ) (i : Fin 2) :
    0 ≤ lemma4SideReferenceProbability θ n i := ENNReal.toReal_nonneg

/-- The actual source two-band construction dominates the product of the
two finite side-reference probabilities and the original annulus-pair mass.
All middle conditioning, association and residual geometry is proved here. -/
theorem lemma4_band_reference_product_lower (θ : Parameters) (n : ℕ) :
    lemma4SideReferenceProbability θ n 0 * lemma4SideReferenceProbability θ n 1 *
      (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅) (lemma4AnnulusPairEvent n)).toReal ≤
    (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal :=
  lemma4_band_construction_lower_of_sideEventIdentity θ n
    (lemma4SideReferenceEvent n) (lemma4SideReferenceEvent_isLowerSet n)
    (lemma4SideReferenceEvent_restriction_iff n)

end
end PottsContinuity.RSW
