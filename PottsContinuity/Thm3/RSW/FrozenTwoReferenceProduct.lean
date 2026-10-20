module

public import PottsContinuity.Thm3.RSW.FrozenPartialEmbeddedLower
public import PottsContinuity.Thm3.RSW.FrozenDecreasingAssociation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance frozenTwoReferenceEdgeEq {Y : Type*} (H : SimpleGraph Y) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Two literal decreasing events on an exact middle fibre have a product
lower bound from their wired reference laws. There is no association assertion
after conditioning only on a mixed geometric event. -/
theorem frozen_two_reference_product_lower_of_closedInteriors
    {Y : Type*} [Finite Y] (H : SimpleGraph Y) (θ : Parameters)
    (ξ : BoundaryCondition Y) (R : Configuration H) (K : RemovedConfiguration H R)
    (D : Set Y)
    (hD : ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃v : Y⦄, v ∈ e.val → v ∈ D)
    (X : Fin 2 → Type*) [hX : ∀ i, Finite (X i)]
    (G : (i : Fin 2) → SimpleGraph (X i)) (f : (i : Fin 2) → X i ↪ Y)
    (hGH : ∀ i, (G i).map (f i) ≤ edgeRestriction H R)
    (B : (i : Fin 2) → Set (X i))
    (hclosed : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → ∀ ⦃y : Y⦄,
      (edgeRestriction H R).Adj (f i x) y → ∃ z : X i, f i z = y ∧ (G i).Adj x z)
    (havoid : ∀ i, ∀ ⦃x : X i⦄, x ∉ B i → f i x ∉ ξ.boundary ∪ D)
    (S : (i : Fin 2) → Set (Configuration (G i))) (hS : ∀ i, IsLowerSet (S i))
    (E : Fin 2 → Set (Configuration H)) (hE : ∀ i, IsLowerSet (E i))
    (hevent : ∀ i, ∀ A : Configuration (edgeRestriction H R),
      (edgeRestrictionConfigurationEquiv H R A).val ∪ K.val ∈ E i ↔
        embeddedConfigurationRestriction (G i) (edgeRestriction H R) (f i) (hGH i) A ∈ S i) :
    (measure (G 0) θ (BoundaryCondition.wired (B 0)) (S 0)).toReal *
      (measure (G 1) θ (BoundaryCondition.wired (B 1)) (S 1)).toReal ≤
      (((law H θ ξ).filter (frozenStateEvent R K)
        (frozenStateEvent_support θ ξ R K)).toMeasure (E 0 ∩ E 1)).toReal := by
  have hlocal (i : Fin 2) := frozen_partial_decreasing_reference_lower_of_closedInterior
    (G i) H (f i) θ ξ R K D hD (hGH i) (B i) (hclosed i) (havoid i)
    (S i) (hS i) (E i) (hevent i)
  exact (mul_le_mul (hlocal 0) (hlocal 1) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg).trans (frozen_decreasing_positive_association
      H θ ξ R K (E 0) (E 1) (hE 0) (hE 1))

end
end PottsContinuity.RSW
