module

public import PottsContinuity.Thm3.RSW.InducedConfinedWitness
public import PottsContinuity.Thm3.RSW.NestedRegionEmbedding

/-! # Confined witnesses in a free induced sample compare with their free window -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
variable {X : Type*} [Finite X] {G : SimpleGraph X}

/-- A witness confined to W under a free law on any induced D has probability
at most its increasing-event probability in the full free window W. D and W
need not contain one another. -/
theorem free_induced_confinedWitness_probability_le (θ : Parameters)
    (D W : Set X) (E : Set (Configuration G)) (hE : IsUpperSet E) :
    (measure (G.induce D) θ (BoundaryCondition.free ∅)
      {A | inducedConfigurationExtension D A ∈ confinedWitnessEvent G W E}).toReal ≤
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {A | inducedConfigurationExtension W A ∈ E}).toReal := by
  let C : Set D := {v | v.val ∈ W}
  let E' : Set (Configuration (G.induce D)) :=
    {A | inducedConfigurationExtension D A ∈ E}
  have hE' : IsUpperSet E' := hE.preimage (inducedConfigurationExtension_monotone D)
  have hfirst : (measure (G.induce D) θ (BoundaryCondition.free ∅)
      {A | inducedConfigurationExtension D A ∈ confinedWitnessEvent G W E}).toReal ≤
      (measure (G.induce D) θ (BoundaryCondition.free ∅)
        (confinedWitnessEvent (G.induce D) C E')).toReal := by
    refine measureReal_mono ?_
    intro A hA
    exact confinedWitness_extension_pullback D W E A hA
  have hlocal := free_confinedWitness_probability_le (G := G.induce D) θ C E' hE'
  let T : Set (Configuration ((G.induce D).induce C)) :=
    {B | inducedConfigurationExtension D (inducedConfigurationExtension C B) ∈ E}
  have hT : IsUpperSet T := hE'.preimage (inducedConfigurationExtension_monotone C)
  have hcmp := embedded_free_probability_le ((G.induce D).induce C) (G.induce W)
    (nestedRegionEmbedding D W) (nestedRegionEmbedding_map_le D W) θ T hT
  refine (hfirst.trans hlocal).trans (hcmp.trans ?_)
  refine measureReal_mono ?_
  intro A hA
  exact hE (nested_induced_extension_restriction_subset D W A) hA

end
end PottsContinuity.RSW
