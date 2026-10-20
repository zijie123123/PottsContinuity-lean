-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EmbeddedClosedInteriorOuterComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryUpper
public import PottsContinuity.FKC.FiniteFK.EmbeddedClosedInteriorOuterBoundary

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- The exact embedded restriction event in an increasing set has outer FK
probability bounded by the wired-interior FK probability when all frozen
exterior pullback partitions are dominated by wiring the interior. The graph
closure and boundary-avoidance premises are explicit; this statement does not
discharge them for any particular corridor. -/
theorem embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hGH : G.map f ≤ H) (q : ClusterWeight) (ξ : BoundaryCondition W)
    (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure H q ξ
      {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal ≤
      (measure G q (BoundaryCondition.wired B) S).toReal := by
  exact embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    G H f hGH q ξ (BoundaryCondition.wired B) S hS (by
      intro K
      exact isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
        f hGH B hclosed ξ hξavoid K)

end
end PottsContinuity.FKC.FiniteFK
