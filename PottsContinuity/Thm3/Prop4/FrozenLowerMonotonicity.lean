module

public import PottsContinuity.Thm3.Prop4.FrozenFiberDualArms
public import PottsContinuity.Thm3.Prop4.LowerBoundaryComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Monotonicity of decreasing events in the revealed open state

The revealed set stays fixed. Its open state changes both the induced boundary
partition and the restored original sample, in the same direction.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance frozenLowerOriginalDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- Opening more revealed original bonds decreases the exact conditional
probability of every lower event in the full restored configuration. -/
theorem frozen_fiber_lower_event_antitone (V : Finset LatticeVertex)
    (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (B C : RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R)
    (hBC : B.val ⊆ C.val)
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex))))
    (hE : IsLowerSet E) :
    ((frozenFiberLaw θ ξ R C).toMeasure {A | A.val ∪ C.val ∈ E}).toReal ≤
    ((frozenFiberLaw θ ξ R B).toMeasure {A | A.val ∪ B.val ∈ E}).toReal := by
  rw [frozen_fiber_event_probability_eq_deleted,frozen_fiber_event_probability_eq_deleted]
  let G := squareLattice.induce (V : Set LatticeVertex)
  let EB : Set (Configuration (edgeRestriction G R)) :=
    {A | (edgeRestrictionConfigurationEquiv G R A).val ∪ B.val ∈ E}
  let EC : Set (Configuration (edgeRestriction G R)) :=
    {A | (edgeRestrictionConfigurationEquiv G R A).val ∪ C.val ∈ E}
  have hEC : IsLowerSet EC := by
    intro A D hDA hA
    exact hE (Finset.union_subset_union
      ((edgeRestrictionConfigurationOrderIso G R).monotone hDA) le_rfl) hA
  have hsub : EC ⊆ EB := by
    intro A hA
    exact hE (Finset.union_subset_union le_rfl hBC) hA
  have hpart : (frozenBoundary ξ B.val).partition ≤ (frozenBoundary ξ C.val).partition :=
    componentSetoid_mono ξ hBC
  exact (finite_FK_lower_boundary_comparison (edgeRestriction G R) θ _ _ hpart EC hEC).trans
    (measureReal_mono hsub (measure_ne_top _ _))

/-- The all-open state of a fixed revealed set is the uniform worst state
for a lower event; no primal-conditioning correlation is asserted. -/
theorem frozen_fiber_lower_event_ge_all_open (V : Finset LatticeVertex)
    (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (B : RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R)
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex))))
    (hE : IsLowerSet E) :
    ((frozenFiberLaw θ ξ R ⟨R,Finset.Subset.refl R⟩).toMeasure
      {A | A.val ∪ R ∈ E}).toReal ≤
    ((frozenFiberLaw θ ξ R B).toMeasure {A | A.val ∪ B.val ∈ E}).toReal :=
  frozen_fiber_lower_event_antitone V θ ξ R B _ B.property E hE

end
end PottsContinuity.Thm3.Prop4
