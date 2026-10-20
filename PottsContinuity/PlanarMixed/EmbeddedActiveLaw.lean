module

public import PottsContinuity.PlanarMixed.OrderedCutActive
public import PottsContinuity.PD.FK.DomainMarkov
public import Mathlib.Tactic
public import PottsContinuity.Thm3.RSW.StoppedConnection
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw

/-!
# Exact active-carrier law from a literal remaining graph

The source reveals the entire complement of the embedded active graph.
The resulting remaining law is transported by an explicit configuration
bijection, retaining the induced boundary and every band vertex. No law
identification or probability estimate is assumed.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section

/-- Frozen actual connections along the embedded arcs give the exact
pullback boundary order needed by the host active-carrier estimate. -/
theorem twoBlockBoundary_le_pullback_frozen_of_arcConnections
    {V W : Type*} [Finite V] (H : SimpleGraph W) (f : V ↪ W)
    (ξ : BoundaryCondition W) (K : Configuration H)
    (A C : Set V) (hAC : Disjoint A C)
    (hA : ∀ u ∈ A, ∀ v ∈ A, ActualConnected H K (f u) (f v))
    (hC : ∀ u ∈ C, ∀ v ∈ C, ActualConnected H K (f u) (f v)) :
    (twoBlockBoundary A C hAC).partition ≤
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K)).partition := by
  intro u v huv
  change (componentSetoid H ξ K).r (f u) (f v)
  rcases (twoBlockBoundary_partition_rel A C hAC u v).mp huv with rfl | huv | huv
  · exact (componentSetoid H ξ K).refl (f u)
  · exact actualConnected_component H ξ K (hA u huv.1 v huv.2)
  · exact actualConnected_component H ξ K (hC u huv.1 v huv.2)

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

end
end PottsContinuity.PlanarMixed
