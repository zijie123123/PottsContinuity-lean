module

public import PottsContinuity.Thm3.Prop4.FiniteDualArmsCorrelation
public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exact fixed-fiber law for reconstructed common dual arms

The normalized original frozen fiber is transported through the proved
finite DMP and the actual deleted-edge graph equivalence. Its correlation
statement applies to that fixed fiber, rather than an unspecified primal event.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance fiberDualArmsOriginalDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- Every original event has exactly its reconstructed deleted-graph probability
under the genuine normalized fixed frozen fiber. -/
theorem frozen_fiber_event_probability_eq_deleted (V : Finset LatticeVertex)
    (θ : Parameters) (ξ : BoundaryCondition (V : Set LatticeVertex))
    (R : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (B : RemovedConfiguration (squareLattice.induce (V : Set LatticeVertex)) R)
    (E : Set (Configuration (squareLattice.induce (V : Set LatticeVertex)))) :
    ((frozenFiberLaw θ ξ R B).toMeasure
      {A | A.val ∪ B.val ∈ E}).toReal =
    (measure (edgeRestriction (squareLattice.induce (V : Set LatticeVertex)) R) θ
      (frozenBoundary ξ B.val)
      ((fun C => (edgeRestrictionConfigurationEquiv _ R C).val ∪ B.val) ⁻¹' E)).toReal := by
  rw [frozenFiberLaw_eq_remainingLaw,← law_edgeRestriction_map]
  rw [PMF.toMeasure_map_apply]
  · rfl
  · exact fun _ _ => MeasurableSpace.measurableSet_top
  · exact MeasurableSpace.measurableSet_top

end
end PottsContinuity.Thm3.Prop4
