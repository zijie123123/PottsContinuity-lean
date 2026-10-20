-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/VolumeComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Disintegration
public import PottsContinuity.FKC.FiniteFK.Expectation
public import PottsContinuity.FKC.FiniteFK.RemainingComparison

/-!
# Comparison of the original FK marginal with a graph with edges deleted

Conditioning on the deleted edges induces a coarser partition than the original
one. The proved conditional law and wiring comparison give the stochastic
comparison after averaging over the actual frozen marginal. All original
vertices are retained here. Comparisons between graphs on different vertex
carriers, through an embedding, are proved in `FKC.FiniteFK.EmbeddedBoundaryUpper`
(`embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition`).
-/

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance volumeComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance volumeComparisonEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance volumeComparisonRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance volumeComparisonFrozenFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

omit [Finite V] in
/-- The frozen open paths only add identifications to the original partition. -/
theorem boundary_le_frozenBoundary (ξ : BoundaryCondition V) (H : Configuration G) :
    ξ.partition ≤ (frozenBoundary ξ H).partition := le_sup_right

omit [Finite V] in
/-- Wiring the entire vertex set dominates every induced boundary relation. -/
theorem frozenBoundary_le_allWired (ξ : BoundaryCondition V) (H : Configuration G) :
    (frozenBoundary ξ H).partition ≤ (BoundaryCondition.wired Set.univ).partition := by
  intro u v _
  exact Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

/-- Deleting edges while keeping the original partition decreases every
nonnegative increasing observable of the edges that remain. -/
theorem remainingLaw_le_original_marginal (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation ((law G q ξ).map (fun C => (configurationSplitEquiv G R C).1)) f := by
  rw [law_map_remaining_eq_bind_frozen]
  apply le_expectation_bind
  intro H
  exact remainingLaw_boundary_comparison G q ξ (frozenBoundary ξ H.val)
    (boundary_le_frozenBoundary ξ H.val) R f hf0 hf

/-- Full wiring on the retained original vertices bounds the original marginal
from above. This is a finite graph comparison, not a boundary-only wiring claim. -/
theorem original_marginal_le_allWired (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation ((law G q ξ).map (fun C => (configurationSplitEquiv G R C).1)) f ≤
      expectation (remainingLaw G q (BoundaryCondition.wired Set.univ) R) f := by
  rw [law_map_remaining_eq_bind_frozen]
  apply expectation_bind_le
  intro H
  exact remainingLaw_boundary_comparison G q (frozenBoundary ξ H.val)
    (BoundaryCondition.wired Set.univ) (frozenBoundary_le_allWired ξ H.val) R f hf0 hf

/-- The comparison expressed directly as an observable of the full original
configuration, without replacing the genuine marginal by a new model. -/
theorem remainingLaw_le_original_expectation (q : ClusterWeight) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation (law G q ξ) (fun C => f (configurationSplitEquiv G R C).1) := by
  simpa only [expectation_map] using remainingLaw_le_original_marginal q ξ R f hf0 hf

end
end PottsContinuity.FKC.FiniteFK
