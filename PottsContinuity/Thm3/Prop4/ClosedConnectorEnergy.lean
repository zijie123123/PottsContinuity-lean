module

public import PottsContinuity.Thm3.Prop4.ClosedCutEnergy
public import PottsContinuity.Thm3.Prop4.FiniteDualArmsCorrelation
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Closing the retained primal connector bonds under the exact finite law

The uniform closed-edge cost holds for every boundary partition. Positive
correlation with a lower event retains both already-constructed dual arms
while closing the prescribed connector set in the same sample.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
attribute [local instance] configurationMeasurableSpace

/-- Every prescribed finite set of original sampled edges can be closed
with the product closed-edge cost under any finite FK boundary law. -/
theorem finite_closed_edges_probability (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) :
    (1-edgeParameter θ)^F.card ≤ (measure G θ ξ {A | Disjoint A F}).toReal := by
  have h := finite_closed_cut_energy G θ ξ F Set.univ (by simp)
  simpa only [Set.univ_inter,measure_univ,ENNReal.toReal_one,mul_one] using h

/-- Retain an arbitrary lower event while closing the actual connector edges,
without an independence premise or any further event conditioning. -/
theorem finite_closed_edges_and_lower (θ : Parameters) (ξ : BoundaryCondition V)
    (F : Finset G.edgeSet) (E : Set (Configuration G)) (hE : IsLowerSet E) :
    (1-edgeParameter θ)^F.card*(measure G θ ξ E).toReal ≤
      (measure G θ ξ ({A | Disjoint A F} ∩ E)).toReal := by
  apply (mul_le_mul_of_nonneg_right (finite_closed_edges_probability G θ ξ F)
    ENNReal.toReal_nonneg).trans
  apply finite_FK_lower_event_correlation G θ ξ _ E _ hE
  intro A C hCA hA
  exact hA.mono_left hCA

end
end PottsContinuity.Thm3.Prop4
