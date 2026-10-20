module

public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)

/-- The increasing event that the actual inner bonds contain the restriction
of SOME original configuration in E. The witness remains a full original
configuration; no conditional law or preferred witness is built into it. -/
def upwardEmbeddedEvent (E : Set (Configuration H)) : Set (Configuration G) :=
  {C | ∃ A ∈ E, embeddedConfigurationRestriction G H f hGH A ⊆ C}

omit [Finite V] [Finite W] in
/-- The event is increasing even when the original event is not increasing. -/
theorem upwardEmbeddedEvent_isUpperSet (E : Set (Configuration H)) :
    IsUpperSet (upwardEmbeddedEvent G H f hGH E) := by
  intro C D hCD hC
  obtain ⟨A,hA,hAC⟩ := hC
  exact ⟨A,hA,hAC.trans hCD⟩

omit [Finite V] [Finite W] in
/-- Every original E-configuration supplies its own honest witness. -/
theorem subset_preimage_upwardEmbeddedEvent (E : Set (Configuration H)) :
    E ⊆ {A | embeddedConfigurationRestriction G H f hGH A ∈
      upwardEmbeddedEvent G H f hGH E} := by
  intro A hA
  exact ⟨A,hA,Finset.Subset.refl _⟩

omit [Finite V] in
/-- Projecting the crossing witness to its actual lower bonds cannot lower
the reference event probability. -/
theorem measure_le_preimage_upwardEmbeddedEvent (θ : Parameters)
    (ξ : BoundaryCondition W) (E : Set (Configuration H)) :
    (measure H θ ξ E).toReal ≤
      (measure H θ ξ {A | embeddedConfigurationRestriction G H f hGH A ∈
        upwardEmbeddedEvent G H f hGH E}).toReal := by
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _)
  exact MeasureTheory.measure_mono (subset_preimage_upwardEmbeddedEvent G H f hGH E)

end
end PottsContinuity.Push
