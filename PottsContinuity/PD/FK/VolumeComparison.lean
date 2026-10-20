-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/FK/VolumeComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `FiniteFK/VolumeComparison.lean`.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsContinuity.PD.FK.Disintegration
public import PottsContinuity.PD.FK.Expectation
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Comparison of the original FK marginal with a graph with edges deleted

Conditioning on the deleted edges induces a coarser partition than the original
one. The proved conditional law and wiring comparison give the stochastic
comparison after averaging over the actual frozen marginal. All original
vertices are retained here. Comparisons between graphs on different vertex
carriers, through an embedding, are proved in `PD.FK.EmbeddedBoundaryUpper`
(`embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition`).
-/

@[expose] public section

namespace PottsContinuity.PD.FK

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

/-- Deleting edges while keeping the original partition decreases every
nonnegative increasing observable of the edges that remain. -/
theorem remainingLaw_le_original_marginal (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation ((law G q ξ).map (fun C => (configurationSplitEquiv G R C).1)) f := by
  rw [law_map_remaining_eq_bind_frozen]
  apply le_expectation_bind
  intro H
  exact remainingLaw_boundary_comparison G q ξ (frozenBoundary ξ H.val)
    (boundary_le_frozenBoundary ξ H.val) R f hf0 hf

/-- The comparison expressed directly as an observable of the full original
configuration, without replacing the genuine marginal by a new model. -/
theorem remainingLaw_le_original_expectation (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    expectation (remainingLaw G q ξ R) f ≤
      expectation (law G q ξ) (fun C => f (configurationSplitEquiv G R C).1) := by
  simpa only [expectation_map] using remainingLaw_le_original_marginal q ξ R f hf0 hf

end
end PottsContinuity.PD.FK
