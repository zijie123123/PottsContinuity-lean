module

public import PottsContinuity.Thm3.RSW.Lemma4DualBands
public import PottsContinuity.Thm3.RSW.MiddleReferenceProduct

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance lemma4MiddleBandEdgeEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

/-- The source two-band joint lower estimate from explicit residual geometry.
The actual middle reveal and visibility of the two annuli are already proved;
there is no conditional marginal or conditional association premise. -/
theorem lemma4_band_construction_lower_of_middleGeometry
    (θ : Parameters) (n : ℕ)
    (X : Fin 2 → Type*) [hX : ∀ i, Finite (X i)]
    (G : (i : Fin 2) → SimpleGraph (X i))
    (f : (i : Fin 2) → X i ↪ {z : LatticeVertex // z ∈ box (56*n)})
    (hGH : ∀ i, (G i).map (f i) ≤ edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n))
    (B : (i : Fin 2) → Set (X i))
    (hclosed : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → ∀ ⦃y : {z : LatticeVertex // z ∈ box (56*n)}⦄,
      (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)).Adj (f i x) y →
        ∃ z : X i, f i z = y ∧ (G i).Adj x z)
    (havoid : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → f i x ∉ lemma4MiddleVertices n)
    (S : (i : Fin 2) → Set (Configuration (G i))) (hS : ∀ i, IsLowerSet (S i))
    (hevent : ∀ K : RemovedConfiguration (lemma4AmbientGraph n) (lemma4MiddleReveal n),
      ∀ i, ∀ A : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)),
      (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val ∪ K.val ∈
        lemma4DualBandEvent n i ↔
      embeddedConfigurationRestriction (G i)
        (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)) (f i) (hGH i) A ∈ S i) :
    (measure (G 0) θ (BoundaryCondition.wired (B 0)) (S 0)).toReal *
      (measure (G 1) θ (BoundaryCondition.wired (B 1)) (S 1)).toReal *
      (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅)
        (lemma4AnnulusPairEvent n)).toReal ≤
      (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal := by
  have h := middle_visible_joint_lower_of_closedInteriors (lemma4AmbientGraph n) θ
    (BoundaryCondition.free ∅) (lemma4MiddleReveal n) (lemma4MiddleVertices n)
    (fun e he v hv => lemma4MiddleReveal_endpoint n he hv)
    X G f hGH B hclosed (by
      intro i x hx
      simpa only [BoundaryCondition.free,Set.empty_union] using havoid i hx)
    S hS (lemma4DualBandEvent n) (lemma4DualBandEvent_isLowerSet n)
    hevent (lemma4AnnulusPairEvent n) (lemma4AnnulusPairEvent_middle_visible n)
  have hset : (lemma4DualBandEvent n 0 ∩ lemma4DualBandEvent n 1) ∩ lemma4AnnulusPairEvent n =
      lemma4BandConstructionEvent n := Set.inter_comm _ _
  rw [hset] at h
  exact h

end
end PottsContinuity.RSW
