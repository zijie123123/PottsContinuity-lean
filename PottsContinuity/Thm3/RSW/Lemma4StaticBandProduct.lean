module

public import PottsContinuity.Thm3.RSW.Lemma4MiddleBandProduct
public import PottsContinuity.Thm3.RSW.Lemma4BandRestoration

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance lemma4StaticMiddleBandEdgeEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

/-- The source two-band joint lower estimate from explicit residual geometry.
The actual middle reveal, annulus visibility and invariance under restoring
ANY middle states are proved. Only static residual graph/event geometry remains. -/
theorem lemma4_band_construction_lower_of_staticMiddleGeometry
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
    (hevent : ∀ i, ∀ A : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)),
      (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val ∈
        lemma4DualBandEvent n i ↔
      embeddedConfigurationRestriction (G i)
        (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)) (f i) (hGH i) A ∈ S i) :
    (measure (G 0) θ (BoundaryCondition.wired (B 0)) (S 0)).toReal *
      (measure (G 1) θ (BoundaryCondition.wired (B 1)) (S 1)).toReal *
      (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅)
        (lemma4AnnulusPairEvent n)).toReal ≤
      (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅)
        (lemma4BandConstructionEvent n)).toReal := by
  apply lemma4_band_construction_lower_of_middleGeometry θ n X G f hGH B hclosed havoid S hS
  intro K i A
  have h := (lemma4DualBandEvent_union_middle_iff n i
    (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val
    K.val K.property).trans (hevent i A)
  constructor
  · intro hA
    apply h.mp
    exact lemma4DualBandEvent_isLowerSet n i (by
      intro e he
      simpa only [Finset.mem_union] using he) hA
  · intro hA
    exact lemma4DualBandEvent_isLowerSet n i (by
      intro e he
      simpa only [Finset.mem_union] using he) (h.mpr hA)

end
end PottsContinuity.RSW
