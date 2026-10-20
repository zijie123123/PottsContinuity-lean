module

public import PottsContinuity.Thm3.RSW.Lemma4StaticBandProduct
public import PottsContinuity.Thm3.RSW.Lemma4SideResidual

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The upper and lower source sides use their actual two orientations. -/
def lemma4SideSign : Fin 2 → ℤ := Fin.cases 1 (fun _ => -1)

theorem lemma4SideSign_eq_one_or_neg_one (i : Fin 2) :
    lemma4SideSign i = 1 ∨ lemma4SideSign i = -1 := by
  refine Fin.cases (Or.inl rfl) (fun _ => Or.inr rfl) i

/-- Source eq13's probability product on the concrete upper/lower residual
graphs. Closure, base-row avoidance, annulus visibility, frozen-state
restoration and fixed-fibre association are all discharged. Only the exact
static sampled event identity with the side reference events remains. -/
theorem lemma4_band_construction_lower_of_sideEventIdentity
    (θ : Parameters) (n : ℕ)
    (S : (i : Fin 2) → Set (Configuration (lemma4SideResidualGraph n (lemma4SideSign i))))
    (hS : ∀ i, IsLowerSet (S i))
    (hevent : ∀ i, ∀ A : Configuration (edgeRestriction (lemma4AmbientGraph n) (lemma4MiddleReveal n)),
      (edgeRestrictionConfigurationEquiv (lemma4AmbientGraph n) (lemma4MiddleReveal n) A).val ∈
        lemma4DualBandEvent n i ↔
      inducedConfigurationRestriction (lemma4SideVertices n (lemma4SideSign i)) A ∈ S i) :
    (measure (lemma4SideResidualGraph n (lemma4SideSign 0)) θ
      (BoundaryCondition.wired (lemma4SideBase n (lemma4SideSign 0))) (S 0)).toReal *
    (measure (lemma4SideResidualGraph n (lemma4SideSign 1)) θ
      (BoundaryCondition.wired (lemma4SideBase n (lemma4SideSign 1))) (S 1)).toReal *
    (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅) (lemma4AnnulusPairEvent n)).toReal ≤
    (measure (lemma4AmbientGraph n) θ (BoundaryCondition.free ∅) (lemma4BandConstructionEvent n)).toReal := by
  exact lemma4_band_construction_lower_of_staticMiddleGeometry θ n
    (fun i => lemma4SideVertices n (lemma4SideSign i))
    (fun i => lemma4SideResidualGraph n (lemma4SideSign i))
    (fun i => inducedVertexEmbedding (lemma4SideVertices n (lemma4SideSign i)))
    (fun i => inducedVertexEmbedding_map_le (lemma4SideVertices n (lemma4SideSign i)))
    (fun i => lemma4SideBase n (lemma4SideSign i))
    (fun i => lemma4SideResidual_closed n _ (lemma4SideSign_eq_one_or_neg_one i))
    (fun i => lemma4SideResidual_avoids_middle n _ (lemma4SideSign_eq_one_or_neg_one i))
    S hS hevent

end
end PottsContinuity.RSW
