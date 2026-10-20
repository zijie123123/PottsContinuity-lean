module

public import PottsContinuity.Thm3.RSW.SeedAvoidingConditional
public import PottsContinuity.Thm3.RSW.StoppingJointUpper

/-! # Free upper product for seed-separated witnesses in overlapping windows -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
local instance seedSeparatedProductEdgeDecidableEq {X : Type*} (G : SimpleGraph X) :
    DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- The two reference regions may overlap. Actual seed-cluster
avoidance replaces the need to choose two disjoint random interiors. The first
event's rooted support makes its entire confinement event record-measurable. -/
theorem free_seedSeparated_confined_product_of_rootedSupport
    {X : Type*} [Finite X] (G : SimpleGraph X) (θ : PD.FK.Parameters)
    (S : Finset X) (W₁ W₂ : Set X)
    (E₁ E₂ : Set (PD.FK.Configuration G))
    (hE₁ : IsUpperSet E₁) (hE₂ : IsUpperSet E₂)
    (hrooted : ∀ B : PD.FK.Configuration G,
      B ∈ E₁ ↔ inducedConfigurationErasure (S : Set X) B ∈ E₁) :
    (PD.FK.measure G θ (PD.FK.BoundaryCondition.free ∅)
      (seedAvoidingConfinedWitnessEvent G S W₂ E₂ ∩
        confinedWitnessEvent G W₁ E₁)).toReal ≤
      (PD.FK.measure (G.induce W₁) θ (PD.FK.BoundaryCondition.free ∅)
        {B | inducedConfigurationExtension W₁ B ∈ E₁}).toReal *
      (PD.FK.measure (G.induce W₂) θ (PD.FK.BoundaryCondition.free ∅)
        {B | inducedConfigurationExtension W₂ B ∈ E₂}).toReal := by
  let c₂ := (measure (G.induce W₂) θ (BoundaryCondition.free ∅)
    {B | inducedConfigurationExtension W₂ B ∈ E₂}).toReal
  have h := stopped_event_inter_upper_of_record_bounds θ (BoundaryCondition.free ∅)
    (FKC.FiniteFK.actualMultiClusterReveal G S)
    (FKC.FiniteFK.actualMultiClusterReveal_consistent S)
    (seedAvoidingConfinedWitnessEvent G S W₂ E₂) (confinedWitnessEvent G W₁ E₁) c₂
    (fun A₀ A hr => rooted_confinedWitnessEvent_seedRecord_iff S W₁ E₁ hrooted A₀ A hr)
    (fun A₀ => seedAvoidingConfinedWitness_record_probability_le θ S W₂ E₂ hE₂ A₀)
  have hfirst := free_confinedWitness_probability_le θ W₁ E₁ hE₁
  have hprod := h.trans (mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ c₂ from ENNReal.toReal_nonneg))
  exact hprod.trans_eq (mul_comm c₂ _)

end
end PottsContinuity.RSW
